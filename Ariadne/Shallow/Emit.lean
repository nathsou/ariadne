import Ariadne.Emit
import Ariadne.Shallow.Elaborate

namespace Ariadne.Shallow
open Core

private def ident (name : String) : String := "«" ++ name ++ "»"

private def typeText : Core.Ty → String
  | .unit => "_root_.Unit"
  | .bool => "_root_.Bool"
  | .int => "_root_.Int"
  | .number => "_root_.Float.Model"
  | .string => "_root_.Ariadne.JSString"
  | .option t => s!"(_root_.Option {typeText t})"
  | .list t => s!"(_root_.List {typeText t})"
  | .pair a b => s!"({typeText a} × {typeText b})"
  | .fn a b => s!"({typeText a} → {typeText b})"
  | .step a b => s!"(_root_.Ariadne.Shallow.Step {typeText a} {typeText b})"
  | .exit a b => s!"(_root_.Ariadne.Shallow.Exit {typeText a} {typeText b})"

private def index : Var Γ t → Nat
  | .here => 0
  | .there v => index v + 1

private def unaryText : Unary a b → String → String
  | .not, a => s!"(!{a})"
  | .intNeg, a => s!"(-{a})"
  | .numNeg, a => s!"(-{a})"
  | .isSome, a => s!"({a}).isSome"
  | .length, xs => s!"(_root_.Float.Model.ofNat ({xs}).length)"
  | .reverse, xs => s!"({xs}).reverse"

private def binaryText : Binary a b c → String → String → String
  | .intAdd, a, b | .numAdd, a, b => s!"({a} + {b})"
  | .intSub, a, b | .numSub, a, b => s!"({a} - {b})"
  | .intMul, a, b | .numMul, a, b => s!"({a} * {b})"
  | .numDiv, a, b => s!"({a} / {b})"
  | .numMod, a, b => s!"(_root_.Ariadne.numberRemainder {a} {b})"
  | .intEq, a, b | .numEq, a, b | .strEq, a, b | .boolEq, a, b => s!"({a} == {b})"
  | .intLt, a, b | .numLt, a, b => s!"(decide ({a} < {b}))"
  | .intLe, a, b | .numLe, a, b => s!"(decide ({a} ≤ {b}))"
  | .intRange, a, b => s!"(_root_.Ariadne.Shallow.Loop.integers {a} {b})"
  | .strAppend, a, b => s!"({a} ++ {b})"
  | .strLt, a, b => s!"(compare {a} {b} == Ordering.lt)"
  | .strLe, a, b => s!"(compare {a} {b} != Ordering.gt)"
  | .and, a, b => s!"({a} && {b})"
  | .or, a, b => s!"({a} || {b})"
  | .append, a, b => s!"({a} ++ {b})"
  | .get, xs, i => s!"(_root_.Ariadne.Shallow.JSArray.get {xs} {i})"

private def closedTerms : Term Γ t → List ((t : Core.Ty) × Term [] t)
  | .closed body => closedTerms body ++ [⟨_, body⟩]
  | .unary _ a | .some a | .fst a | .snd a | .lam _ a | .next a | .stop a | .ret a => closedTerms a
  | .binary _ a b | .let_ _ a b | .cons a b | .pair a b | .app a b => closedTerms a ++ closedTerms b
  | .ite a b c | .optionCase a b c | .each a b c | .exitCase a b c => closedTerms a ++ closedTerms b ++ closedTerms c
  | .listMap a b | .listFilter a b | .listSome a b | .listEvery a b |
      .listFind a b | .listFindIndex a b => closedTerms a ++ closedTerms b
  | .listReduce a b c | .listSlice a b c => closedTerms a ++ closedTerms b ++ closedTerms c
  | _ => []

private def closedKey (body : Term [] t) : String := reprStr t ++ reprStr body

private def joinName (label : String) (keys : List String) (body : Term [] t) : String :=
  ident s!"{label}#{keys.idxOf (closedKey body)}"

private def coreText (label : String) (keys : List String) : Term Γ t → String
  | .closed body => s!"(Core.Term.closed JoinCore.{joinName label keys body})"
  | .var v => s!"(Core.Term.var ({reprStr v}))"
  | .unit => "Core.Term.unit"
  | .bool b => s!"(Core.Term.bool {b})"
  | .int n => s!"(Core.Term.int ({n}))"
  | .number m e => s!"(Core.Term.number {m} ({e}))"
  | .string s => s!"(Core.Term.string {reprStr s})"
  | .unary op a => s!"(Core.Term.unary ({reprStr op}) {coreText label keys a})"
  | .binary op a b => s!"(Core.Term.binary ({reprStr op}) {coreText label keys a} {coreText label keys b})"
  | @Term.let_ _ t _ name a b => s!"(Core.Term.let_ (a := {reprStr t}) {reprStr name} {coreText label keys a} {coreText label keys b})"
  | .ite a b c => s!"(Core.Term.ite {coreText label keys a} {coreText label keys b} {coreText label keys c})"
  | .none => "Core.Term.none"
  | .some a => s!"(Core.Term.some {coreText label keys a})"
  | .optionCase a b c => s!"(Core.Term.optionCase {coreText label keys a} {coreText label keys b} {coreText label keys c})"
  | .nil => "Core.Term.nil"
  | .cons a b => s!"(Core.Term.cons {coreText label keys a} {coreText label keys b})"
  | .pair a b => s!"(Core.Term.pair {coreText label keys a} {coreText label keys b})"
  | .fst a => s!"(Core.Term.fst {coreText label keys a})"
  | .snd a => s!"(Core.Term.snd {coreText label keys a})"
  | .lam name body => s!"(Core.Term.lam {reprStr name} {coreText label keys body})"
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
  | .exitCase a b c => s!"(Core.Term.exitCase {coreText label keys a} {coreText label keys b} {coreText label keys c})"

private def termText (label : String) (keys : List String) (term : Term Γ t) (names : List String) (depth : Nat := 0) : String :=
  match term with
  | .var v => names[index v]?.getD "invalid_variable"
  | .unit => "()"
  | .bool b => toString b
  | .int n => s!"({n} : _root_.Int)"
  | .number m e => s!"(_root_.Float.Model.ofScientific {m} ({e}))"
  | .string s => s!"({reprStr s} : _root_.Ariadne.JSString)"
  | .unary op a => unaryText op (termText label keys a names depth)
  | .binary op a b => binaryText op (termText label keys a names depth) (termText label keys b names depth)
  | @Term.let_ _ t _ name a b =>
    let name := ident s!"_{name}#{depth}"
    s!"(let {name} : {typeText t} := {termText label keys a names depth};\n{termText label keys b (name :: names) (depth + 1)})"
  | .ite c a b => s!"(if {termText label keys c names depth} then\n{termText label keys a names depth}\nelse\n{termText label keys b names depth})"
  | .none => "_root_.Option.none"
  | .some a => s!"(_root_.Option.some {termText label keys a names depth})"
  | .optionCase a b c =>
    let name := ident s!"value#{depth}"
    s!"(_root_.Option.elim {termText label keys a names depth} {termText label keys b names depth} (fun {name} => {termText label keys c (name :: names) (depth + 1)}))"
  | .nil => "[]"
  | .cons a b => s!"({termText label keys a names depth} :: {termText label keys b names depth})"
  | .pair a b => s!"({termText label keys a names depth}, {termText label keys b names depth})"
  | .fst a => s!"({termText label keys a names depth}).1"
  | .snd a => s!"({termText label keys a names depth}).2"
  | @Term.lam a _ _ name body =>
    let name := ident s!"_{name}#{depth}"
    s!"(fun {name} : {typeText a} => {termText label keys body (name :: names) (depth + 1)})"
  | .app f a => s!"({termText label keys f names depth} {termText label keys a names depth})"
  | .closed body => s!"JoinNative.{joinName label keys body}"
  | .listMap f xs => s!"(_root_.Ariadne.Shallow.JSArray.map {termText label keys f names depth} {termText label keys xs names depth})"
  | .listFilter f xs => s!"(_root_.Ariadne.Shallow.JSArray.filter {termText label keys f names depth} {termText label keys xs names depth})"
  | .listReduce f a xs => s!"(_root_.Ariadne.Shallow.JSArray.reduce {termText label keys f names depth} {termText label keys a names depth} {termText label keys xs names depth})"
  | .listSome f xs => s!"(_root_.Ariadne.Shallow.JSArray.some {termText label keys f names depth} {termText label keys xs names depth})"
  | .listEvery f xs => s!"(_root_.Ariadne.Shallow.JSArray.every {termText label keys f names depth} {termText label keys xs names depth})"
  | .listFind f xs => s!"(_root_.Ariadne.Shallow.JSArray.find {termText label keys f names depth} {termText label keys xs names depth})"
  | .listFindIndex f xs => s!"(_root_.Ariadne.Shallow.JSArray.findIndex {termText label keys f names depth} {termText label keys xs names depth})"
  | .listSlice xs a b => s!"(_root_.Ariadne.Shallow.JSArray.slice {termText label keys xs names depth} {termText label keys a names depth} {termText label keys b names depth})"
  | .next a => s!"(_root_.Ariadne.Shallow.Step.next {termText label keys a names depth})"
  | .stop a => s!"(_root_.Ariadne.Shallow.Step.stop {termText label keys a names depth})"
  | .ret a => s!"(_root_.Ariadne.Shallow.Step.ret {termText label keys a names depth})"
  | .each xs init body => s!"(_root_.Ariadne.Shallow.Loop.each {termText label keys xs names depth} {termText label keys init names depth} {termText label keys body names depth})"
  | .exitCase e done ret => s!"(_root_.Ariadne.Shallow.Exit.elim {termText label keys e names depth} {termText label keys done names depth} {termText label keys ret names depth})"

def emit (source : String) (program : Program) (namespace_ : String) : Checked String := do
  if !program.classes.isEmpty then
    Elaborate.refusal "A5102" "class extraction is not implemented yet" program.classes.head!.span
  if program.functions.isEmpty then
    Elaborate.refusal "A5101" "there are no functions to extract" {}
  let mut out := (Ariadne.emit source program namespace_).replace
    "import Ariadne.Certificate\n" "import Ariadne.Certificate\nimport Ariadne.Shallow.Elaborate\n"
  out := out ++ "\n-- Shallow denotation certificates. Operational adequacy is not yet proved.\n" ++
    s!"namespace {namespace_}.Shallow\nopen Ariadne Ariadne.Shallow\nset_option linter.unusedSimpArgs false\n\n"
  for f in program.functions do
    let core ← Elaborate.function program f.name
    let coreName := "CoreArtifacts." ++ ident f.name
    let functionName := ident f.name
    let names := f.params.map (fun param => ident s!"{param.name}#arg")
    let params := String.join ((names.zip core.params).map fun (name, t) => s!" ({name} : {typeText t})")
    let joins := (closedTerms core.body).foldl (fun acc entry =>
      if acc.any (fun other => closedKey other.2 == closedKey entry.2) then acc else acc ++ [entry]) []
    let keys := joins.map fun ⟨_, body⟩ => closedKey body
    let mut checks : List String := []
    for ⟨t, join⟩ in joins do
      let j := joinName f.name keys join
      let code := (coreText f.name keys join).replace "\n" " "
      let native := (termText f.name keys join []).replace "\n" "\n  "
      out := out ++ s!"def JoinCore.{j} : Core.Term [] ({reprStr t}) := {code}\n\n"
      out := out ++ s!"@[simp] def JoinNative.{j} : {typeText t} :=\n  {native}\n\n"
      out := out ++ s!"theorem JoinChecks.{j} : Denote.term JoinCore.{j} () = JoinNative.{j} := by\n" ++
        s!"  unfold {namespace_}.Shallow.JoinNative.{j}\n" ++
        s!"  simp only [JoinCore.{j}, Denote.term, Core.Var.get" ++
        String.join (checks.map (", " ++ ·)) ++ "] <;> rfl\n\n"
      checks := checks ++ [s!"JoinChecks.{j}"]
    let body := (termText f.name keys core.body names).replace "\n" "\n  "
    let data := (coreText f.name keys core.body).replace "\n" " "
    let paramData := (reprStr core.params).replace "\n" " "
    let resultData := (reprStr core.result).replace "\n" " "
    out := out ++ s!"def {coreName} : Core.Function := " ++
      s!"\u007b params := {paramData}, result := {resultData}, body := {data} \u007d\n\n"
    out := out ++ s!"theorem {"ElaborationChecks." ++ ident f.name} :\n" ++
      s!"    Elaborate.function _root_.{namespace_}.program {reprStr f.name} = .ok {coreName} := by kernel_rfl\n\n"
    out := out ++ s!"def {functionName}{params} : {typeText core.result} :=\n  {body}\n\n"
    let envName := if core.params.isEmpty then "_env" else "env"
    let args := String.join ((List.range core.params.length).map fun i =>
      " (" ++ envName ++ String.join (List.replicate i ".2") ++ ".1)")
    out := out ++ s!"theorem {"DenotationChecks." ++ ident f.name} :\n" ++
      s!"    (fun {envName} : Core.Env {coreName}.params => {functionName}{args}) =\n" ++
      s!"      Denote.function {coreName} := by\n" ++
      s!"  unfold {namespace_}.Shallow.{functionName}\n" ++
      s!"  simp only [Denote.function, {coreName}, Denote.term, Core.Var.get" ++
      String.join (checks.map (", " ++ ·)) ++ "] <;> rfl\n\n"
  return out ++ s!"end {namespace_}.Shallow\n"

end Ariadne.Shallow
