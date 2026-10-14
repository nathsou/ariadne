import Lean

/-!
# The soundness gate

`Ariadne.Audit.run` checks a built Lean project and fails unless:

1. **Every declaration of the project re-checks with Lean's kernel.** The project's constants are replayed
   into an environment holding only what the project imports, so nothing added around the kernel (an
   option, an environment extension) is believed.
2. **Theorems use only the standard axioms** (`propext`, `Classical.choice`, `Quot.sound`; `sorry` and
   `native_decide` show up as axioms), and nothing they depend on in the project is `partial`, `unsafe`,
   opaque, `implemented_by` or `extern`. The locked definitions are held to the same rule, so what runs
   compiled (for differential tests) is what the proofs reason about.
3. **Statements are proved exactly** (optional): every proposition defined under a specification namespace
   has a theorem of the same name under a proofs namespace, whose type is exactly that proposition.
4. **The locked declarations are unchanged.** The lock file holds, for every locked declaration, its
   statement, and for a definition its body (or, for a recursive one, a fingerprint of it, since the
   compiled form is unreadable). Declarations Lean derived and the locked ones use (a mutual
   definition's compiled body, matchers) are recorded by fingerprint. A change shows up as a change to that file, to review;
   `--write-lock` rewrites it.

A project configures what the lock holds: the declarations under some namespaces or of some modules, and
named ones, with the project's definitions they use, transitively. Theorems are left out (equation
lemmas appear only when a proof first needs them), except the statements locked by name.
-/

namespace Ariadne.Audit

open Lean Meta

structure Config where
  /-- The modules to load. -/
  modules : Array Name
  /-- The project's root namespaces: their modules are replayed, and their theorems audited. -/
  project : List Name
  /-- Lock every declaration of the modules under these prefixes. -/
  lockModules : List Name := []
  /-- Lock every declaration under these namespaces. -/
  lockNamespaces : List Name := []
  /-- Lock these declarations. -/
  lockNames : List Name := []
  /-- Lock the statements (not the proofs) of these theorems. -/
  lockStatements : List Name := []
  /-- Propositions defined under the first namespace must be proved exactly by the theorem of the same
  name under the second. -/
  specs : Option (Name × Name) := none
  lockPath : System.FilePath
  lockHeader : String

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def moduleOf? (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.map fun i => env.header.moduleNames[i.toNat]!

/-- Whether Lean derived the declaration from another (left out of the lock). -/
def derived (env : Environment) (n : Name) : Bool :=
  n.isInternal || Meta.isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n ||
    (match n with
     | .str _ s => s == "ctorIdx" || s == "noConfusionType" || s == "eq_def" || s.startsWith "eq_" ||
        s == "brecOn" || s == "below" || s == "binductionOn" || s == "ibelow" || s == "sizeOf_spec" ||
        s.startsWith "_" || s == "induct" || s == "mutual_induct"
     | _ => false) ||
    (match env.find? n with | some (.recInfo _) => true | _ => false)

/-- Whether a definition's value is (structurally or well-foundedly) recursive. -/
def recursive (v : Expr) : Bool :=
  (v.find? fun e => match e with
    | .const n _ => (match n with | .str _ s => s == "brecOn" || s == "fix" | _ => false) || n == ``WellFounded.fix
    | _ => false).isSome

unsafe def run (cfg : Config) (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let write := args.contains "--write-lock"
  let mut failures : Array String := #[]
  let env ← importModules (cfg.modules.map fun m => { module := m }) {} (loadExts := true)
  let inProject (m : Name) := cfg.project.contains m.getRoot
  let ours (n : Name) := (moduleOf? env n).any inProject

  -- 1. Replay every project declaration through the kernel, on top of what the project imports.
  let mut imports : Array Import := #[]
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for (m, data) in env.header.moduleNames.zip env.header.moduleData do
    if !inProject m then continue
    for i in data.imports do
      if !inProject i.module && !(imports.any (·.module == i.module)) then imports := imports.push i
    for c in data.constants do constants := constants.insert c.name c
  let base ← importModules imports {}
  try
    discard <| Lean.Kernel.Environment.replay constants base.toKernelEnv
  catch e => failures := failures.push s!"kernel replay: {e}"

  -- What the lock holds: its roots, and the project's definitions they use, transitively.
  let mut roots : Array Name := cfg.lockNames.toArray
  for (n, _) in env.constants.map₁.toList do
    if !ours n || derived env n then continue
    let inModule := (moduleOf? env n).any fun m => cfg.lockModules.any (·.isPrefixOf m)
    if inModule || cfg.lockNamespaces.any (·.isPrefixOf n) then roots := roots.push n
  let mut locked : NameSet := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if locked.contains n then continue
    let some ci := env.find? n | failures := failures.push s!"{n} is missing"; continue
    if ci matches .thmInfo _ && !Meta.isInstanceCore env n then continue
    locked := locked.insert n
    let mut uses := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
    if let .inductInfo i := ci then
      for c in i.ctors do
        if let some cc := env.find? c then uses := uses ++ cc.type.getUsedConstants
    -- Derived declarations are followed too (a mutual definition's body lives in its derived `_mutual`),
    -- and recorded by fingerprint.
    for c in uses do
      if ours c && !locked.contains c then todo := todo.push c

  -- 2. Axioms of every theorem, and what theorems and locked definitions depend on in the project.
  let mut count := 0
  todo := locked.toArray
  for (n, ci) in env.constants.map₁.toList do
    if ours n && ci matches .thmInfo _ then
      count := count + 1
      todo := todo.push n
      let (axioms, _) ← (collectAxioms n : CoreM _).toIO { fileName := "audit", fileMap := default } { env }
      for a in axioms do
        if !allowedAxioms.contains a then failures := failures.push s!"{n} depends on the axiom {a}"
  let mut seen : NameSet := {}
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if ci.isUnsafe then failures := failures.push s!"{n} is unsafe"
    if ci matches .opaqueInfo _ then failures := failures.push s!"{n} is opaque (partial?)"
    if (Compiler.implementedByAttr.getParam? env n).isSome || isExtern env n then
      failures := failures.push s!"{n} is implemented_by or extern"
    for c in ci.getUsedConstantsAsSet do
      if ours c && !seen.contains c then todo := todo.push c

  -- 3. Statements proved exactly.
  let mut specCount := 0
  if let some (spec, proofs) := cfg.specs then
    for (n, ci) in env.constants.map₁.toList do
      if !(spec.isPrefixOf n) || n.isInternal then continue
      let .defnInfo d := ci | continue
      if d.type != .sort 0 then continue
      specCount := specCount + 1
      let p := proofs ++ n.replacePrefix spec .anonymous
      match env.find? p with
      | some (.thmInfo t) => if t.type != .const n [] then failures := failures.push s!"{p} doesn't prove exactly {n}"
      | _ => failures := failures.push s!"{n} has no theorem {p}"

  -- 4. The lock.
  let statements := cfg.lockStatements.toArray.qsort Name.lt
  let names := locked.toArray.qsort Name.lt
  let ppOpts : Options := ({} : Options).set `pp.fullNames true |>.set `pp.proofs true |>.set `pp.width 120
  let print (n : Name) (statementOnly : Bool) : IO String := do
    let some ci := env.find? n | return s!"\n{n} is missing\n"
    if derived env n then
      return s!"\n{n} -- derived; fingerprint {ci.type.hash} {(ci.value?.map (·.hash)).getD 0}\n"
    let txt : MetaM String := do
      let t ← ppExpr ci.type
      let body ← match ci with
        | .defnInfo d =>
          if statementOnly then pure ""
          else if recursive d.value then pure s!" :=\n  -- recursive; fingerprint {d.value.hash}"
          else pure s!" :=\n  {← ppExpr d.value}"
        | .inductInfo i => do
          let mut s := ""
          for c in i.ctors do
            if let some cc := env.find? c then s := s ++ s!"\n  | {c} : {← ppExpr cc.type}"
          pure s
        | _ => pure ""
      pure s!"\n{n} : {t}{body}\n"
    let (s, _, _) ← txt.toIO { fileName := "audit", fileMap := default, options := ppOpts } { env }
    return s
  let mut lock := cfg.lockHeader ++ "\n"
  if !statements.isEmpty then lock := lock ++ "\n-- Statements\n"
  for n in statements do
    if !(env.find? n matches some (.thmInfo _)) then failures := failures.push s!"{n} is not a theorem"
    lock := lock ++ (← print n true)
  lock := lock ++ "\n-- Definitions\n"
  for n in names do lock := lock ++ (← print n false)
  if write then
    IO.FS.writeFile cfg.lockPath lock
    IO.println s!"wrote {cfg.lockPath}"
  else
    let current ← if ← cfg.lockPath.pathExists then IO.FS.readFile cfg.lockPath else pure ""
    if current != lock then
      failures := failures.push s!"{cfg.lockPath} is not what the locked declarations are: review the change, then run the audit with --write-lock"

  if failures.isEmpty then
    let specs := if cfg.specs.isSome then s!"; {specCount} statements proved exactly" else ""
    IO.println s!"Audit passed: every declaration re-checks with the kernel; {count} theorems use only standard axioms{specs}; {names.size + statements.size} locked declarations match {cfg.lockPath}."
    return 0
  for f in failures do IO.eprintln s!"✗ {f}"
  return 1

end Ariadne.Audit
