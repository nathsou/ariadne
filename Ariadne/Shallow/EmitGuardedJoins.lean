import Ariadne.Shallow.Elaborate
import Ariadne.Shallow.Adequacy.GuardedJoinsContext

namespace Ariadne.Shallow.GuardedJoinEmit
open Core

private def compactRepr {α : Type} [Repr α] (value : α) : String := (repr value).pretty 10000000

private def ident (name : String) : String := "«" ++ name ++ "»"

private def scalarKind : Core.Ty → Option String
  | .unit => some ".unit"
  | .bool => some ".bool"
  | .int => some ".int"
  | .number => some ".number"
  | .string => some ".string"
  | _ => none

private def scalarValue : Core.Ty → String → Option String
  | .unit, _ => some "Value.undefined"
  | .bool, value => some s!"(Value.boolean {value})"
  | .int, value => some s!"(Value.bigint {value})"
  | .number, value => some s!"(Value.number {value})"
  | .string, value => some s!"(Value.string {value})"
  | _, _ => none


private def index : Var Γ t → Nat
  | .here => 0
  | .there v => index v + 1

private def unaryRuleText : Unary a b → String → Option String
  | .not, "!" => some ".not"
  | .intNeg, "-" => some ".intNeg"
  | .numNeg, "-" => some ".numNeg"
  | _, _ => none

private def binaryRuleText : Binary a b c → String → Option String
  | .intAdd, "+" => some ".intAdd" | .intSub, "-" => some ".intSub" | .intMul, "*" => some ".intMul"
  | .intEq, "===" => some ".intEq" | .intLt, "<" => some ".intLt" | .intLe, "<=" => some ".intLe"
  | .numAdd, "+" => some ".numAdd" | .numSub, "-" => some ".numSub" | .numMul, "*" => some ".numMul"
  | .numDiv, "/" => some ".numDiv" | .numMod, "%" => some ".numMod"
  | .numEq, "===" => some ".numEq" | .numLt, "<" => some ".numLt" | .numLe, "<=" => some ".numLe"
  | .strAppend, "+" => some ".strAppend" | .strEq, "===" => some ".strEq"
  | .strLt, "<" => some ".strLt" | .strLe, "<=" => some ".strLe" | .boolEq, "===" => some ".boolEq"
  | _, _ => none

private def swappedRuleText : Binary a b c → String → Option String
  | .intLt, ">" => some ".intGt" | .intLe, ">=" => some ".intGe"
  | .numLt, ">" => some ".numGt" | .numLe, ">=" => some ".numGe"
  | .strLt, ">" => some ".strGt" | .strLe, ">=" => some ".strGe"
  | _, _ => none

/-- Print correspondence witnesses only for rules with a proved operational
interpretation. The Lean kernel checks the witness against the source AST and
the emitted Core term, so this printer is not a semantic oracle. -/
private def scalarProof (names : List String) : Expr → Term Γ t → Option String
  | .literal .undefined _, .unit => some ".unit _"
  | .literal (.boolean a) _, .bool b => if a == b then some ".bool _ _" else none
  | .literal (.bigint a) _, .int b => if a == b then some ".int _ _" else none
  | .literal (.number a e) _, .number b f => if a == b && e == f then some ".number _ _ _" else none
  | .literal (.string a) _, .string b => if a == b then some ".string _ _" else none
  | .var name _, .var v => do
    if names[index v]? != some name then none else
      return s!".var {← scalarKind t} ({compactRepr v}) _ (by decide)"
  | .unary source arg _, .unary op value => do
    let rule ← unaryRuleText op source
    return s!".unary {rule} ({← scalarProof names arg value}) _"
  | .binary source lhs rhs _, .binary op a b => do
    if let some rule := binaryRuleText op source then
      return s!".binary {rule} ({← scalarProof names lhs a}) ({← scalarProof names rhs b}) _"
    let rule ← swappedRuleText op source
    return s!".binarySwap {rule} ({← scalarProof names lhs b}) ({← scalarProof names rhs a}) _"
  | .conditional condition yes no _, .ite c a b => do
    return s!".conditional ({← scalarProof names condition c}) ({← scalarProof names yes a}) ({← scalarProof names no b}) _"
  | .binary "&&" lhs rhs _, .ite a b (.bool false) => do
    return s!".and ({← scalarProof names lhs a}) ({← scalarProof names rhs b}) _"
  | .binary "||" lhs rhs _, .ite a (.bool true) b => do
    return s!".or ({← scalarProof names lhs a}) ({← scalarProof names rhs b}) _"
  | .unary "!" arg _, .ite a (.bool false) (.bool true) => do
    return s!".notIte ({← scalarProof names arg a}) _"
  | expression, .ite a (.bool true) (.bool false) => do
    return s!".boolIte ({← scalarProof names expression a})"
  | _, _ => none
termination_by structural _ term => term

private def guardedScalarKind : Core.Ty → Option String
  | .int53 => some ".int53"
  | t => scalarKind t

private def guardedScalarValue : Core.Ty → String → Option String
  | .int53, value => some s!"(Value.number (Float.Model.ofInt {value}))"
  | t, value => scalarValue t value

private def scalarCoreProof : Term Γ t → Option String
  | .var v => do return s!".var {← guardedScalarKind t} ({compactRepr v})"
  | .unit => some ".unit"
  | .bool _ => some ".bool _"
  | .int _ => some ".int _"
  | .number _ _ => some ".number _ _"
  | .string _ => some ".string _"
  | @Term.unary a b _ op value => do
    return s!".unary (sa := {← guardedScalarKind a}) (sb := {← guardedScalarKind b}) ({compactRepr op}) ({← scalarCoreProof value})"
  | @Term.binary a b c _ op left right => do
    return s!".binary (sa := {← guardedScalarKind a}) (sb := {← guardedScalarKind b}) (sc := {← guardedScalarKind c}) " ++
      s!"({compactRepr op}) ({← scalarCoreProof left}) ({← scalarCoreProof right})"
  | @Term.let_ _ a b name value body => do
    return s!".let_ (sa := {← guardedScalarKind a}) (sb := {← guardedScalarKind b}) {compactRepr name} " ++
      s!"({← scalarCoreProof value}) ({← scalarCoreProof body})"
  | .ite condition yes no => do
    return s!".ite ({← scalarCoreProof condition}) ({← scalarCoreProof yes}) ({← scalarCoreProof no})"
  | .closed body => do return s!".closed ({← scalarCoreProof body})"
  | _ => none

private def comparisonRuleText : Binary .int .int t → String → Option String
  | .intEq, "===" => some ".eq"
  | .intLt, "<" => some ".lt"
  | .intLe, "<=" => some ".le"
  | _, _ => none

private def mathRuleText : Unary a t → String → Option String
  | .numAbs, "abs" => some ".abs"
  | .numFloor, "floor" => some ".floor"
  | .numTrunc, "trunc" => some ".trunc"
  | _, _ => none

private def guardedProof (names : List String) : Expr → Term Γ t → Option String
  | source, .binary .guard (.binary .numBitsEq number (.unary .int53ToNumber (.unary .intToInt53 _))) (.unary .intToInt53 value) => do
    return s!".integer ({← scalarCoreProof value}) ({← guardedProof names source number})"
  | source, .unary .int53ToNumber value => do
    return s!".widen ({← guardedProof names source value})"
  | .binary source left right _, .binary op (.unary .int53ToInt a) (.unary .int53ToInt b) => do
    let rule ← comparisonRuleText op source
    return s!".compare {rule} ({← guardedProof names left a}) ({← guardedProof names right b}) _"
  | .call (.member (.var "Math" _) method _) [arg] _, .unary op term => do
    let rule ← mathRuleText op method
    return s!".math {rule} ({← guardedProof names arg term}) _ _ _"
  | .var name _, .var v => do
    if names[index v]? != some name then none else
      return s!".total (.var {← guardedScalarKind t} ({compactRepr v}) _ (by decide))"
  | .unary source arg _, .unary op value => do
    let rule ← unaryRuleText op source
    return s!".unary {rule} ({← guardedProof names arg value}) _"
  | .binary source left right _, .binary op a b => do
    let rule ← binaryRuleText op source
    return s!".binary {rule} ({← guardedProof names left a}) ({← guardedProof names right b}) _"
  | .conditional condition yes no _, .ite test a b => do
    return s!".conditional ({← guardedProof names condition test}) ({← guardedProof names yes a}) ({← guardedProof names no b}) _"
  | source, term => do return s!".total ({← scalarProof names source term})"
termination_by structural _ term => term


private def variableText : Nat → String
  | 0 => "Core.Var.here"
  | n + 1 => s!"(Core.Var.there {variableText n})"


private def inputProof (count : Nat) : String :=
  let rec casesFor (remaining : Nat) (indent : String) : String :=
    match remaining with
    | 0 => indent ++ "cases v\n"
    | n + 1 =>
      indent ++ "cases v with\n" ++ indent ++ "| here =>\n" ++ indent ++ "  cases scalar\n" ++
      String.join (List.replicate n (indent ++ "  apply Adequacy.lookup_declare_other (by decide)\n")) ++
      indent ++ "  exact Adequacy.lookup_declare_self _ _ _\n" ++
      indent ++ "| there v =>\n" ++ casesFor n (indent ++ "  ")
  "    intro t v scalar _visible\n" ++ casesFor count "    "


private def closedTerms : Term Γ t → List ((t : Core.Ty) × Term [] t)
  | .closed body => closedTerms body ++ [⟨_, body⟩]
  | .unary _ a | .some a | .fst a | .snd a | .lam _ a | .next a | .stop a | .ret a | .inl a | .inr a | .pack _ a | .unpack a => closedTerms a
  | .binary _ a b | .let_ _ a b | .cons a b | .pair a b | .app a b | .recursive a b => closedTerms a ++ closedTerms b
  | .ite a b c | .optionCase a b c | .each a b c | .measured a b c | .exitCase a b c | .mapSet a b c | .sumCase a b c => closedTerms a ++ closedTerms b ++ closedTerms c
  | .listMap a b | .listFilter a b | .listSome a b | .listEvery a b |
      .listFind a b | .listFindIndex a b => closedTerms a ++ closedTerms b
  | .listReduce a b c | .listSlice a b c => closedTerms a ++ closedTerms b ++ closedTerms c
  | _ => []

private def closedKey (body : Term [] t) : String := compactRepr t ++ compactRepr body

private def joinName (label : String) (keys : List String) (body : Term [] t) : String :=
  ident s!"{label}#{keys.idxOf (closedKey body)}"

private def coreText (label : String) (keys : List String) : Term Γ t → String
  | .closed body => s!"(Core.Term.closed JoinCore.{joinName label keys body})"
  | .var v => s!"(Core.Term.var ({compactRepr v}))"
  | .unit => "Core.Term.unit"
  | .bool b => s!"(Core.Term.bool {b})"
  | .int n => s!"(Core.Term.int ({n}))"
  | .number m e => s!"(Core.Term.number {m} ({e}))"
  | .string s => s!"(Core.Term.string {compactRepr s})"
  | .unary op a => s!"(Core.Term.unary ({compactRepr op}) {coreText label keys a})"
  | .binary op a b => s!"(Core.Term.binary ({compactRepr op}) {coreText label keys a} {coreText label keys b})"
  | @Term.let_ _ t _ name a b => s!"(Core.Term.let_ (a := {compactRepr t}) {compactRepr name} {coreText label keys a} {coreText label keys b})"
  | .ite a b c => s!"(Core.Term.ite {coreText label keys a} {coreText label keys b} {coreText label keys c})"
  | .none => "Core.Term.none"
  | .some a => s!"(Core.Term.some {coreText label keys a})"
  | .optionCase a b c => s!"(Core.Term.optionCase {coreText label keys a} {coreText label keys b} {coreText label keys c})"
  | .nil => "Core.Term.nil"
  | .cons a b => s!"(Core.Term.cons {coreText label keys a} {coreText label keys b})"
  | .pair a b => s!"(Core.Term.pair {coreText label keys a} {coreText label keys b})"
  | .fst a => s!"(Core.Term.fst {coreText label keys a})"
  | .snd a => s!"(Core.Term.snd {coreText label keys a})"
  | .lam name body => s!"(Core.Term.lam {compactRepr name} {coreText label keys body})"
  | .app f a => s!"(Core.Term.app {coreText label keys f} {coreText label keys a})"
  | .listMap f xs => s!"(Core.Term.listMap {coreText label keys f} {coreText label keys xs})"
  | .listFilter f xs => s!"(Core.Term.listFilter {coreText label keys f} {coreText label keys xs})"
  | .listReduce f a xs => s!"(Core.Term.listReduce {coreText label keys f} {coreText label keys a} {coreText label keys xs})"
  | .listSome f xs => s!"(Core.Term.listSome {coreText label keys f} {coreText label keys xs})"
  | .listEvery f xs => s!"(Core.Term.listEvery {coreText label keys f} {coreText label keys xs})"
  | .listFind f xs => s!"(Core.Term.listFind {coreText label keys f} {coreText label keys xs})"
  | .listFindIndex f xs => s!"(Core.Term.listFindIndex {coreText label keys f} {coreText label keys xs})"
  | .listSlice xs a b => s!"(Core.Term.listSlice {coreText label keys xs} {coreText label keys a} {coreText label keys b})"
  | .next a => s!"(Core.Term.next {coreText label keys a})"
  | .stop a => s!"(Core.Term.stop {coreText label keys a})"
  | .ret a => s!"(Core.Term.ret {coreText label keys a})"
  | .each a b c => s!"(Core.Term.each {coreText label keys a} {coreText label keys b} {coreText label keys c})"
  | .measured a b c => s!"(Core.Term.measured {coreText label keys a} {coreText label keys b} {coreText label keys c})"
  | .recursive a b => s!"(Core.Term.recursive {coreText label keys a} {coreText label keys b})"
  | .exitCase a b c => s!"(Core.Term.exitCase {coreText label keys a} {coreText label keys b} {coreText label keys c})"
  | @Term.mapEmpty _ k v => s!"(Core.Term.mapEmpty (k := {compactRepr k}) (v := {compactRepr v}))"
  | .setEmpty => "Core.Term.setEmpty"
  | .mapSet m k v => s!"(Core.Term.mapSet {coreText label keys m} {coreText label keys k} {coreText label keys v})"
  | .inl a => s!"(Core.Term.inl {coreText label keys a})"
  | .inr a => s!"(Core.Term.inr {coreText label keys a})"
  | .sumCase a b c => s!"(Core.Term.sumCase {coreText label keys a} {coreText label keys b} {coreText label keys c})"
  | .pack declaration a => s!"(Core.Term.pack ({compactRepr declaration}) {coreText label keys a})"
  | .unpack a => s!"(Core.Term.unpack {coreText label keys a})"


private structure Entry where
  name : String
  ty : Core.Ty
  ghost : Option String := none

private structure Frame where
  saved : String
  names : List String

private structure Context where
  program : String
  entries : List Entry
  names : String
  ghosts : String
  active : List String
  frames : List Frame := []

private def Context.frameText (ctx : Context) : String :=
  "[" ++ String.intercalate ", " (ctx.frames.map fun frame =>
    s!"\u007b names := {compactRepr frame.names}, saved := {frame.saved} \u007d") ++ "]"

private def Context.pre (ctx : Context) : String :=
  s!"(Adequacy.GuardedJoinContext {ctx.program} ({ctx.names}) ({ctx.ghosts}) ({compactRepr ctx.active}) {ctx.frameText})"

private def Context.elaborator (ctx : Context) : Elaborate.Context :=
  ctx.entries.map (fun entry => Elaborate.binding entry.name entry.ty)

private def Context.scalar (ctx : Context) (name : String) (ty : Core.Ty) (declare : Bool) : Context :=
  { ctx with
    entries := {name, ty} :: ctx.entries
    names := s!"(({ctx.names}).cons {compactRepr name})"
    ghosts := s!"(Adequacy.Ghosts.skip ({ctx.ghosts}))"
    active := if declare then name :: ctx.active else ctx.active }

private structure Target where
  functionName : String
  continuation : String
  context : Context
  resumeSource : List Stmt
  inline : Bool := false

private structure Resolution where
  context : Context
  result : Core.Ty
  types : List Core.Ty
  term : Core.Term types result

private structure Printer where
  label : String
  keys : List String
  next : Nat := 0
  definitions : List String := []
  resolutions : List (String × Resolution) := []
  sourceSuffixes : List (String × String) := []
  captures : List (String × (String × String)) := []
  outsides : List (String × String) := []

private abbrev PrintM := StateT Printer Option

private def fresh (kind : String) : PrintM String := do
  let state ← get
  set {state with next := state.next + 1}
  return "SourceJoinChecks." ++ ident s!"{state.label}#{kind}{state.next}"

private def add (definition : String) : PrintM Unit := modify fun state =>
  {state with definitions := state.definitions ++ [definition]}

private def casesTree : List String → String → String
  | [], indent => indent ++ "cases v\n"
  | leaf :: rest, indent =>
    indent ++ "cases v with\n" ++ indent ++ "| here => " ++ leaf ++ "\n" ++
    indent ++ "| there v =>\n" ++ casesTree rest (indent ++ "  ")

private def variablePattern : Nat → String
  | 0 => ".here"
  | n + 1 => s!"(.there {variablePattern n})"

private def argumentIndices : Term Γ t → Option (List Nat)
  | .unit => some []
  | .pair (.var v) rest => return index v :: (← argumentIndices rest)
  | _ => none

private def captureProof (current target : Context) (indices : List Nat) : PrintM (String × String) := do
  if indices.length != target.entries.length then failure
  let key := compactRepr (current.names, current.ghosts, current.entries.map Entry.ty, target.names, target.ghosts, target.entries.map Entry.ty, indices)
  if let some (_, cached) := (← get).captures.find? (fun entry => entry.1 == key) then return cached
  let selector ← fresh "select"
  let proof ← fresh "capture"
  let types := target.entries.map Entry.ty
  let arms := indices.zipIdx |>.map fun (i, j) => s!"  | _, {variablePattern j} => {variableText i}\n"
  add (s!"def {selector} : Core.Renaming ({compactRepr types}) ({compactRepr (current.entries.map Entry.ty)})\n" ++
    (if arms.isEmpty then "  | _, v => nomatch v\n\n" else String.join arms ++ "\n"))
  add (s!"theorem {proof} : Adequacy.Captures ({current.names}) ({current.ghosts})\n" ++
    s!"    ({target.names}) ({target.ghosts}) {selector} := by\n" ++
    "  constructor\n  · intro t v repr visible\n" ++
    casesTree (types.map fun _ => "first | exact ⟨rfl, rfl⟩ | (solve | cases visible) | (solve | cases repr)") "    " ++
    "  · intro t v value found\n" ++
    casesTree (types.map fun _ => "first | exact found | cases found") "    " ++ "\n")
  modify fun state => {state with captures := (key, (selector, proof)) :: state.captures}
  return (selector, proof)

private def outsideProof (target : Context) (frame : Frame) : PrintM String := do
  let key := compactRepr (target.names, target.entries.map Entry.ty, frame.names)
  if let some (_, cached) := (← get).outsides.find? (fun entry => entry.1 == key) then return cached
  let proof ← fresh "outside"
  add (s!"theorem {proof} " ++ "{t}" ++
    s!" (v : Core.Var ({compactRepr (target.entries.map Entry.ty)}) t) (repr : Adequacy.Scalar t)\n" ++
    s!"    (visible : ({target.names}).visible v = true) : ({target.names}).get v ∈ ({compactRepr frame.names}) := by\n" ++
    casesTree (target.entries.map fun entry =>
      s!"first | exact (show {compactRepr entry.name} ∈ ({compactRepr frame.names}) from by decide) | (solve | cases visible) | (solve | cases repr)") "  " ++ "\n")
  modify fun state => {state with outsides := (key, proof) :: state.outsides}
  return proof

private def capturedContext (ctx : Context) : PrintM Context := do
  let entries := ctx.entries.foldl (fun out entry =>
    if out.any (fun other => other.name == entry.name) then out else out ++ [entry]) []
  let names ← fresh "names"
  let ghosts ← fresh "ghosts"
  let ghostCode := entries.foldr (fun entry rest => match entry.ghost with
    | none => s!"(Adequacy.Ghosts.skip {rest})"
    | some continuation => s!"(Adequacy.Ghosts.bind {continuation}.abstract {rest})") "Adequacy.Ghosts.empty"
  add s!"def {names} : Adequacy.Names ({compactRepr (entries.map Entry.ty)}) := Adequacy.Names.fromList ({compactRepr (entries.map Entry.name)})\n\n"
  add s!"def {ghosts} : Adequacy.Ghosts ({compactRepr (entries.map Entry.ty)}) := {ghostCode}\n\n"
  return {ctx with entries, names, ghosts}

private def withTarget (statements : List Stmt) (target : Option Target) : List Stmt :=
  statements ++ (target.map Target.resumeSource).getD []

private def nativeTarget (name continuation : String) (context : Context) : Target :=
  {functionName := name, continuation, context,
    resumeSource := [.return_ (.call (.var name {})
      (context.entries.map fun entry => .var entry.name {}) {}) {}]}

private def printJump (ctx : Context) (target : Target) (term : Term Γ t) : PrintM String := do
  let (indices, native, target) ← if target.inline then do
      let resolved ← match (← get).resolutions.find? (fun entry => entry.1 == target.continuation) with
        | some (_, resolution) => pure resolution
        | none => do
          let names ← fresh "inlineNames"
          add s!"def {names} : Adequacy.Names ({compactRepr Γ}) := ({ctx.names}).restrict ({compactRepr target.context.active})\n\n"
          let after := {ctx with names, active := target.context.active, frames := target.context.frames}
          let state ← get
          add s!"def {target.continuation} : Core.Term ({compactRepr Γ}) ({compactRepr t}) := {coreText state.label state.keys term}\n\n"
          let resolution : Resolution := ⟨after, t, Γ, term⟩
          modify fun state => {state with resolutions := (target.continuation, resolution) :: state.resolutions}
          pure resolution
      -- A flattened suffix is captured at its actual Core boundary. Keeping the
      -- original SSA order also keeps every nested closed join unchanged.
      if compactRepr term != compactRepr resolved.term || ctx.entries.length != resolved.context.entries.length then failure
      pure (List.range ctx.entries.length, none, {target with context := resolved.context})
    else do
      let .app (.var fn) argument := term | failure
      let some entry := ctx.entries[index fn]? | failure
      if entry.name != target.functionName || entry.ghost != some target.continuation then failure
      let indices ← argumentIndices argument
      pure (indices, some (compactRepr fn), target)
  let (selector, capture) ← captureProof ctx target.context indices
  if ctx.frames.length < target.context.frames.length then failure
  let closing := ctx.frames.take (ctx.frames.length - target.context.frames.length)
  let mut adapt := s!"(h.capture {capture})"
  let mut finish := "state"
  for frame in closing do
    let outside ← outsideProof target.context frame
    adapt := s!"({adapt}.restore (fun v repr visible => {outside} v repr visible))"
    finish := s!"\u007b {finish} with env := {frame.saved} \u007d"
  let head := match native with
    | some fn => s!"Adequacy.GuardedJoins.contextJump ({fn}) (by rfl) {selector}"
    | none => s!"Adequacy.GuardedJoins.contextInlineExit (continuation := {target.continuation}) {selector} (by rfl)"
  return s!"({head} (fun state => {finish}) (by\n" ++
    s!"  intro state env model h\n  exact {adapt}))"

private def sourceText (statements : List Stmt) : PrintM String := do
  let key := compactRepr statements
  return ((← get).sourceSuffixes.find? (fun entry => entry.1 == key)).map Prod.snd |>.getD key

/-- A suffix theorem is checked once. Its explicit indices prevent recursive
elaboration from repeatedly unfolding every downstream branch certificate. -/
private def nameCertificate (ctx : Context) (target : Option Target) (statements : List Stmt)
    (term : String) (result : Core.Ty) (proof : String) : PrintM String := do
  let name ← fresh "suffix"
  let source ← sourceText statements
  let post ← match target with
    | none => pure "(fun _ _ => False)"
    | some target => do
      let target ← if target.inline then do
        let some (_, resolved) := (← get).resolutions.find? (fun entry => entry.1 == target.continuation) | failure
        pure {target with context := resolved.context}
      else pure target
      if ctx.frames.length < target.context.frames.length then failure
      let closing := ctx.frames.take (ctx.frames.length - target.context.frames.length)
      let finish := closing.foldl (fun state frame => s!"\u007b {state} with env := {frame.saved} \u007d") "state"
      pure s!"(fun state value => Adequacy.GuardedResume {target.context.pre} {target.continuation} ({finish}) value)"
  let params := String.join (ctx.frames.map fun frame => s!" ({frame.saved} : Ariadne.Env)")
  let args := String.join (ctx.frames.map fun frame => " " ++ frame.saved)
  add (s!"theorem {name}{params} :\n" ++
    s!"    Adequacy.GuardedJoins {ctx.program} Interpretation.value {← guardedScalarKind result} {ctx.pre} {post} ({source}) {term} := by\n" ++
    s!"  exact {proof}\n\n")
  return s!"({name}{args})"

/-- This printer is untrusted: all continuations, captures, source shapes and
scope checks are subsequently checked by ScalarJoins' kernel-verified rules. -/
private def statementsProof (program : Program) : Nat → Context → Option Target → List Stmt → Term Γ t → PrintM String
  | 0, _, _, _, _ => failure
  | fuel + 1, ctx, target, statements, term => do
    if statements.isEmpty then
      let some target := target | failure
      return ← printJump ctx target term
    let statement :: rest := statements | failure
    let shared : PrintM String := match term with
    | @Term.let_ _ a _ "join" value branches =>
      match statement with
      | .block .. | .if_ .. => do
        let nextCtx ← capturedContext ctx
        let .ok continuation := Elaborate.statements program 1024 nextCtx.elaborator (withTarget rest target) t | failure
        let name ← fresh "continuation"
        let state ← get
        if !(closedTerms continuation).all (fun entry => state.keys.contains (closedKey entry.2)) then failure
        add s!"def {name} : Core.Term ({compactRepr (nextCtx.entries.map Entry.ty)}) ({compactRepr t}) := {coreText state.label state.keys continuation}\n\n"
        -- Check the exact abstraction shape before printing a witness. The Lean
        -- theorem will check this again against the actual emitted body.
        if compactRepr value != compactRepr (continuation.abstract : Term [] (.fn (environmentType (Elaborate.Types nextCtx.elaborator)) t)) then
          failure
        let joinName := "#joinProof" ++ toString state.next
        let branchCtx : Context := {ctx with
          entries := {name := joinName, ty := a, ghost := some name} :: ctx.entries,
          names := s!"(({ctx.names}).cons {compactRepr joinName})",
          ghosts := s!"(Adequacy.Ghosts.bind {name}.abstract ({ctx.ghosts}))"}
        let next ← statementsProof program fuel nextCtx target rest continuation
        let next ← nameCertificate nextCtx target rest name t next
        let branch ← statementsProof program fuel branchCtx (some (nativeTarget joinName name nextCtx)) [statement] branches
        return s!"(Adequacy.GuardedJoins.contextShared (leading := {compactRepr [statement]}) (continuation := {name})\n" ++
          s!"  (suffixPre := {nextCtx.pre}) {compactRepr joinName} {next} {branch})"
      | _ => failure
    | _ => failure
    shared <|> do
      match statement, term with
      | .return_ expression _ , term =>
        let expressionProof ← guardedProof (ctx.entries.map Entry.name) expression term
        return s!"(Adequacy.GuardedJoins.contextReturn ({expressionProof}) _ _)"
      | .let_ _ name _ expression _, @Term.let_ _ a _ coreName value body =>
        if name != coreName || name == "Math" then failure
        let expressionProof ← guardedProof (ctx.entries.map Entry.name) expression value
        let next ← statementsProof program fuel (ctx.scalar name a true) target rest body
        return s!"(Adequacy.GuardedJoins.contextLet {compactRepr name} (by decide) ({expressionProof}) (by simp) {next} _ _ _)"
      | .assign (.var name _) expression _, @Term.let_ _ a _ coreName value body =>
        if name != coreName then failure
        let some position := ctx.entries.findIdx? (·.name == name) | failure
        if (ctx.entries[position]?).map Entry.ty != some a then failure
        let expressionProof ← guardedProof (ctx.entries.map Entry.name) expression value
        let next ← statementsProof program fuel (ctx.scalar name a false) target rest body
        return s!"(Adequacy.GuardedJoins.contextAssign ({variableText position}) (by decide) ({expressionProof}) {next} _ _)"
      | .if_ condition yes no _, .ite test a b =>
        let expressionProof ← guardedProof (ctx.entries.map Entry.name) condition test
        let yesProof ← statementsProof program fuel ctx target (yes :: rest) a
        let noProof ← statementsProof program fuel ctx target (no :: rest) b
        return s!"(Adequacy.GuardedJoins.contextIf ({expressionProof}) {yesProof} {noProof} _)"
      | .block [] _, term =>
        let next ← statementsProof program fuel ctx target rest term
        return s!"(Adequacy.GuardedJoins.emptyBlock {next} _)"
      | .block inner _, term =>
        let saved := "_scope" ++ toString (← get).next
        modify fun state => {state with next := state.next + 1}
        let bodyCtx := {ctx with frames := {saved, names := ctx.active} :: ctx.frames}
        if rest.isEmpty then
          let body ← statementsProof program fuel bodyCtx target inner term
          return s!"(Adequacy.GuardedJoins.contextBlock (fun {saved} => {body}) _)"
        else if Check.exits 1024 statement then
          let body ← statementsProof program fuel bodyCtx none inner term
          return s!"(Adequacy.GuardedJoins.contextStoppedBlock (fun {saved} => {body}) _ _)"
        else
          let name ← fresh "inline"
          let exitTarget : Target := {
            functionName := ""
            continuation := name
            context := ctx
            resumeSource := withTarget rest target
            inline := true }
          let leading ← statementsProof program fuel ctx (some exitTarget) [statement] term
          let some (_, resolved) := (← get).resolutions.find? (fun entry => entry.1 == name) | failure
          let next ← statementsProof program fuel resolved.context target rest resolved.term
          let next ← nameCertificate resolved.context target rest name resolved.result next
          return s!"(Adequacy.GuardedJoins.resume (leading := {compactRepr [statement]}) (continuation := {name})\n" ++
            s!"  (suffixPre := {resolved.context.pre}) {leading} {next})"
      | _, _ => failure

/-- Emit a source theorem for guarded scalar control using canonical typed
join/scope contexts. Failure leaves unsupported shapes explicit. -/
def sourceTheorem (program : Program) (namespace_ : String) (f : Ariadne.Function) (core : Core.Function)
    (params : String) (names : List String) (safeEnv : String) (publicAlias : Bool) : Option String := do
  let .block statements blockSpan := f.body | none
  if f.params.any (·.name == "Math") || program.functions.any (fun f => ["Math.abs", "Math.floor", "Math.trunc"].contains f.name) then none else pure ()
  let kind ← guardedScalarKind core.result
  let _ ← core.params.mapM guardedScalarKind
  let args ← (core.params.zip names).mapM fun (ty, name) => guardedScalarValue ty name
  let encoded ← guardedScalarValue core.result s!"({ident f.name}{String.join (names.map (" " ++ ·))})"
  let args := "[" ++ String.intercalate ", " args ++ "]"
  let checkName := s!"SourceChecks.{ident f.name}"
  let theoremName := if publicAlias then ident (f.name ++ "_source") else s!"{checkName}.source"
  let coreName := s!"CoreArtifacts.{ident f.name}"
  let entries := (f.params.zip core.params).map fun (param, ty) => ({name := param.name, ty} : Entry)
  let ctx : Context := {
    program := s!"_root_.{namespace_}.certificate.program"
    entries := entries
    names := checkName ++ ".names"
    ghosts := "Adequacy.Ghosts.empty"
    active := (f.params.map Param.name).reverse }
  let joins := (closedTerms core.body).foldl (fun acc entry =>
    if acc.any (fun other => closedKey other.2 == closedKey entry.2) then acc else acc ++ [entry]) []
  let (proof, emitted) ← (statementsProof program 2048 ctx none statements core.body).run
    {label := f.name, keys := joins.map fun entry => closedKey entry.2,
      sourceSuffixes := (List.range (statements.length + 1)).map fun i =>
        (compactRepr (statements.drop i), s!"({checkName}.statements.drop {i})")}
  let functionData := (compactRepr f).replace "\n" " "
  let statementData := checkName ++ ".statements"
  return s!"def {checkName}.function : Ariadne.Function := {functionData}\n\n" ++
    s!"def {checkName}.statements : List Stmt := match {checkName}.function.body with | .block body _ => body | _ => []\n\n" ++
    s!"def {checkName}.names : Adequacy.Names {coreName}.params :=\n" ++
    s!"  Adequacy.Names.fromList {compactRepr (f.params.map Param.name)}\n\n" ++
    String.join emitted.definitions ++
    s!"theorem {checkName}.translated :\n" ++
    s!"    Adequacy.GuardedJoins {ctx.program} Interpretation.value {kind} {ctx.pre} (fun _ _ => False) ({statementData}) {coreName}.body := by\n" ++
    s!"  exact {proof}\n\n" ++
    s!"theorem {theoremName}{params} (heap : Heap) (safe : {ident f.name}.safe{String.join (names.map (" " ++ ·))}) :\n" ++
    s!"    SourceReturnsFrom _root_.{namespace_}.source {compactRepr f.name} heap {args} {encoded} := by\n" ++
    s!"  have inputs : Adequacy.Environment {checkName}.names\n" ++
    s!"      (Adequacy.bindArguments \u007b heap \u007d {checkName}.function.params {args})\n" ++
    s!"      (interp := Interpretation.value) {safeEnv} := by\n" ++ inputProof core.params.length ++
    s!"  have resultEq : {ident f.name}{String.join (names.map (" " ++ ·))} = Denote.term {coreName}.body {safeEnv} :=\n" ++
    s!"    congrFun DenotationChecks.{ident f.name} {safeEnv}\n" ++
    "  rw [resultEq]\n" ++
    s!"  exact Adequacy.guarded_joins_source _root_.{namespace_}.certificate {checkName}.function {kind} {coreName}.body\n" ++
    s!"    ({statementData}) ({compactRepr blockSpan})\n" ++
    s!"    (by kernel_rfl) (by kernel_rfl) Interpretation.value {ctx.pre} {checkName}.translated {safeEnv} (Safety.liftEnvironment {coreName}.params (by decide) {safeEnv}) heap {args}\n" ++
    s!"    (Adequacy.GuardedJoinContext.initial inputs (Adequacy.bindArguments_valid _ _ _) rfl\n" ++
    s!"      (Safety.scalar_lift_environment {coreName}.params (by decide) {safeEnv}) (by constructor <;> rfl)) safe.2\n\n"

end Ariadne.Shallow.GuardedJoinEmit
