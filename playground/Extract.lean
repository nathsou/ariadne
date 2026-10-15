import Lean

/-!
# What Lean says about the examples, for the playground

`lake exe extract OUT.json ROOT FILE` elaborates a Lean file (an example's generated translation and its
proofs) the way `lean` does, and records for the page:

- `hovers`: each identifier, with a local's type, and for a constant its signature and docstring
  (in `consts`, once per constant);
- `goals`: each tactic's goals before and after it, as the infoview shows them;
- `theorems`: each theorem's statement, docstring, line and the axioms it depends on;
- `messages`: errors and warnings (CI requires there are none).

Positions are Lean's: 1-based lines and 0-based columns in Unicode code points. The page cannot
elaborate Lean, so this is what it shows for the examples as written; it says so once they are edited.
-/

open Lean Elab Meta

namespace Extract

def posJson (map : FileMap) (pos : String.Pos.Raw) : Json :=
  let p := map.toPosition pos
  Json.arr #[toJson p.line, toJson p.column]

def rangeJson (map : FileMap) (r : Syntax.Range) : List (String × Json) :=
  [("start", posJson map r.start), ("stop", posJson map r.stop)]

def fmt (f : MessageData) : IO String := do
  return (← f.toString).trimAscii.toString

/-- The hover of an identifier: a local's name and type, or a constant's name (its type and docstring
go in the file's table of constants, `consts`). -/
def hover (ci : ContextInfo) (ti : TermInfo) : IO (Option (List (String × Json) × Option Name)) := do
  unless ti.stx.getKind == identKind || ti.isBinder do return none
  match ti.expr with
  | .const n _ => return some ([("name", toJson n.toString), ("kind", toJson "const")], some n)
  | .fvar id =>
    let some decl := ti.lctx.find? id | return none
    let ty ← ci.runMetaM ti.lctx do
      return (← ppExpr (← instantiateMVars decl.type)).pretty 100
    return some ([("name", toJson decl.userName.eraseMacroScopes.toString), ("type", toJson ty),
      ("kind", toJson "local")], none)
  | _ => return none

/-- A constant's type and docstring. -/
def constJson (env : Environment) (ci : ContextInfo) (n : Name) : IO Json := do
  let ty ← ci.runMetaM {} do
    return (← (PrettyPrinter.ppSignature n)).fmt.pretty 100
  let doc ← findDocString? env n
  return Json.mkObj <| [("signature", toJson ty)] ++ (doc.map fun d => [("doc", toJson d.trimAscii.toString)]).getD []

/-- A tactic's goals, before and after it. -/
def goals (ci : ContextInfo) (ti : TacticInfo) : IO (List (String × Json)) := do
  let show_ (mctx : MetavarContext) (gs : List MVarId) : IO Json := do
    let texts ← gs.mapM fun g => ({ ci with mctx }).runMetaM {} do return (← ppGoal g).pretty 100
    return toJson texts
  return [("before", ← show_ ti.mctxBefore ti.goalsBefore), ("after", ← show_ ti.mctxAfter ti.goalsAfter)]

def runCore (env : Environment) (map : FileMap) (x : CoreM α) : IO α := do
  let (a, _) ← x.toIO { fileName := "", fileMap := map, options := {} } { env }
  return a

def theorems (env : Environment) (map : FileMap) (mainModule : Name) : IO (Array Json) := do
  let mut out := #[]
  for (name, info) in env.constants.map₂.toList do
    let .thmInfo _ := info | continue
    if name.isInternalDetail then continue
    let some ranges ← runCore env map (findDeclarationRanges? name) | continue
    let statement ← runCore env map do
      return (← (PrettyPrinter.ppSignature name).run').fmt.pretty 100
    let axioms ← runCore env map (collectAxioms name)
    let doc ← findDocString? env name
    out := out.push <| Json.mkObj <| [("name", toJson name.toString), ("line", toJson ranges.range.pos.line),
      ("statement", toJson statement), ("axioms", toJson (axioms.map toString)),
      ("module", toJson mainModule.toString)] ++ (doc.map fun d => [("doc", toJson d)]).getD []
  return out.qsort fun a b => (a.getObjValAs? Nat "line").toOption.getD 0 < (b.getObjValAs? Nat "line").toOption.getD 0

def processFile (path : System.FilePath) (moduleName : Name) : IO Json := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx (mainModule := moduleName)
  let env := env.setMainModule moduleName
  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages {})
  let env := s.commandState.env
  let map := inputCtx.fileMap
  let mut hovers : Std.HashMap (Nat × Nat) Json := {}
  let mut consts : Std.HashMap Name Json := {}
  let mut tactics : Array Json := #[]
  for tree in s.commandState.infoState.trees do
    let infos := tree.collectNodesBottomUp fun ci i _ rest => (ci, i) :: rest
    for (ci, i) in infos do
      let some r := i.range? | continue
      match i with
      | .ofTermInfo ti =>
        if hovers.contains (r.start.byteIdx, r.stop.byteIdx) then continue
        if let some (h, c?) ← hover ci ti then
          hovers := hovers.insert (r.start.byteIdx, r.stop.byteIdx) (Json.mkObj (rangeJson map r ++ h))
          if let some c := c? then
            unless consts.contains c do consts := consts.insert c (← constJson env ci c)
      | .ofTacticInfo ti =>
        -- Tactic sequences repeat their children's goals; keep the tactics themselves.
        if ti.stx.getKind == nullKind || ti.stx.getKind == ``Parser.Tactic.tacticSeq1Indented ||
            ti.stx.getKind == ``Parser.Tactic.tacticSeq then continue
        tactics := tactics.push (Json.mkObj (rangeJson map r ++ (← goals ci ti)))
      | _ => pure ()
  let messages ← s.commandState.messages.toList.filterMapM fun m => do
    if m.severity == .information then return none
    return some <| Json.mkObj [("severity", toJson (if m.severity == .error then "error" else "warning")),
      ("pos", Json.arr #[toJson m.pos.line, toJson m.pos.column]), ("text", toJson (← fmt m.data))]
  return Json.mkObj [("hovers", Json.arr (hovers.toArray.map (·.2))), ("goals", Json.arr tactics),
    ("consts", Json.mkObj (consts.toList.map fun (n, j) => (n.toString, j))),
    ("theorems", Json.arr (← theorems env map moduleName)), ("messages", Json.arr messages.toArray)]

/-- The module a file under a source root defines: `Examples/Clamp/Proofs.lean` is `Examples.Clamp.Proofs`. -/
def moduleOf (root : System.FilePath) (path : System.FilePath) : Name :=
  let rel := (path.toString.drop (root.toString.length + 1)).toString
  let parts := ((rel.dropEnd 5).toString.splitOn "/")
  parts.foldl Name.str .anonymous

end Extract

/-- `extract OUT.json ROOT FILE`: the file, a module under the source root `ROOT`. One file per process:
Lean imports modules only once per process. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [out, root, file] := args | IO.eprintln "usage: extract OUT.json ROOT FILE"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let path : System.FilePath := root ++ "/" ++ file
  let data ← Extract.processFile path (Extract.moduleOf root path)
  let mut failed := false
  if let .arr ms := data.getObjValD "messages" then
    for m in ms do
      IO.eprintln s!"{path}: {m.compress}"
      if m.getObjValD "severity" == toJson "error" then failed := true
  IO.FS.writeFile out data.compress
  return if failed then 1 else 0
