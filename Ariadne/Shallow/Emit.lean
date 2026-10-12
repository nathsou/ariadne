import Ariadne.Emit
import Ariadne.Shallow.Elaborate
import Ariadne.Shallow.Safety

namespace Ariadne.Shallow
open Core

private def ident (name : String) : String := "«" ++ name ++ "»"

private def keyText : Key → String
  | .int | .int53 => "_root_.Int"
  | .number => "_root_.Float.Model"
  | .string => "_root_.Ariadne.JSString"
  | .bool => "_root_.Bool"

private def mapNamespace (k : Key) : String :=
  if k == .number then "_root_.Ariadne.Shallow.NumberMap" else "_root_.Ariadne.Shallow.JSMap"
private def setNamespace (k : Key) : String :=
  if k == .number then "_root_.Ariadne.Shallow.NumberSet" else "_root_.Ariadne.Shallow.JSSet"

private def typeText : Core.Ty → String
  | .unit => "_root_.Unit"
  | .bool => "_root_.Bool"
  | .int | .int53 => "_root_.Int"
  | .number => "_root_.Float.Model"
  | .string => "_root_.Ariadne.JSString"
  | .option t => s!"(_root_.Option {typeText t})"
  | .list t => s!"(_root_.List {typeText t})"
  | .map .number v => s!"(_root_.Ariadne.Shallow.NumberMap {typeText v})"
  | .map k v => s!"(_root_.Ariadne.Shallow.JSMap {keyText k} {typeText v})"
  | .set .number => "_root_.Ariadne.Shallow.NumberSet"
  | .set k => s!"(_root_.Ariadne.Shallow.JSSet {keyText k})"
  | .pair a b => s!"({typeText a} × {typeText b})"
  | .sum a b => s!"(_root_.Sum {typeText a} {typeText b})"
  | .named declaration => s!"NativeTypes.{ident declaration.name}"
  | .fn a b => s!"({typeText a} → {typeText b})"
  | .step a b => s!"(_root_.Ariadne.Shallow.Step {typeText a} {typeText b})"
  | .exit a b => s!"(_root_.Ariadne.Shallow.Exit {typeText a} {typeText b})"

private def index : Var Γ t → Nat
  | .here => 0
  | .there v => index v + 1

private def unaryText : Unary a b → String → String
  | .intToInt53, a | .int53ToInt, a => a
  | .int53ToNumber, a => s!"(_root_.Float.Model.ofInt {a})"
  | .intSafe, a => s!"(decide ((-9007199254740991 : Int) ≤ {a} ∧ {a} ≤ 9007199254740991))"
  | .intAbs, a => s!"(Int.ofNat ({a}).natAbs)"
  | .lengthInt53, xs => s!"(Int.ofNat ({xs}).length)"
  | @Unary.mapSizeInt53 k _, value => s!"(Int.ofNat ({mapNamespace k}.size {value}))"
  | @Unary.setSizeInt53 k, value => s!"(Int.ofNat ({setNamespace k}.size {value}))"
  | .not, a => s!"(!{a})"
  | .intNeg, a => s!"(-{a})"
  | .numNeg, a => s!"(-{a})"
  | .numTrunc, a => s!"(_root_.Ariadne.Builtins.numberTrunc {a})"
  | .numFloor, a => s!"(_root_.Ariadne.Builtins.numberFloor {a})"
  | .numAbs, a => s!"({a}).abs"
  | .intToNumber, a => s!"(_root_.Float.Model.ofInt {a})"
  | .isSome, a => s!"({a}).isSome"
  | .length, xs => s!"(_root_.Float.Model.ofNat ({xs}).length)"
  | .reverse, xs => s!"({xs}).reverse"
  | @Unary.mapSize k _, value => s!"(_root_.Float.Model.ofNat ({mapNamespace k}.size {value}))"
  | @Unary.mapKeys k _, value => s!"({mapNamespace k}.keys {value})"
  | @Unary.mapValues k _, value => s!"({mapNamespace k}.values {value})"
  | @Unary.mapEntries k _, value => s!"({mapNamespace k}.entries {value})"
  | @Unary.setSize k, value => s!"(_root_.Float.Model.ofNat ({setNamespace k}.size {value}))"
  | @Unary.setValues k, value => s!"({setNamespace k}.values {value})"
  | @Unary.setEntries k, value => s!"({setNamespace k}.entries {value})"

private def binaryText : Binary a b c → String → String → String
  | .guard, _, value => value
  | .intTdiv, a, b => s!"(Int.tdiv {a} {b})"
  | .intFdiv, a, b => s!"(Int.fdiv {a} {b})"
  | .intTmod, a, b => s!"(Int.tmod {a} {b})"
  | .numBitsEq, a, b => s!"(({a}).toBits == ({b}).toBits)"
  | .int53Range, a, b => s!"(_root_.Ariadne.Shallow.Loop.integers {a} {b})"
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
  | @Binary.mapGet k _, value, key => s!"({mapNamespace k}.get {value} {key})"
  | @Binary.mapHas k _, value, key => s!"({mapNamespace k}.has {value} {key})"
  | @Binary.mapDelete k _, value, key => s!"({mapNamespace k}.delete {value} {key})"
  | @Binary.setHas k, value, key => s!"({setNamespace k}.has {value} {key})"
  | @Binary.setAdd k, value, key => s!"({setNamespace k}.add {value} {key})"
  | @Binary.setDelete k, value, key => s!"({setNamespace k}.delete {value} {key})"

private def closedTerms : Term Γ t → List ((t : Core.Ty) × Term [] t)
  | .closed body => closedTerms body ++ [⟨_, body⟩]
  | .unary _ a | .some a | .fst a | .snd a | .lam _ a | .next a | .stop a | .ret a | .inl a | .inr a | .pack _ a | .unpack a => closedTerms a
  | .binary _ a b | .let_ _ a b | .cons a b | .pair a b | .app a b => closedTerms a ++ closedTerms b
  | .ite a b c | .optionCase a b c | .each a b c | .exitCase a b c | .mapSet a b c | .sumCase a b c => closedTerms a ++ closedTerms b ++ closedTerms c
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
  | .mapEmpty => "Core.Term.mapEmpty"
  | .setEmpty => "Core.Term.setEmpty"
  | .mapSet m k v => s!"(Core.Term.mapSet {coreText label keys m} {coreText label keys k} {coreText label keys v})"
  | .inl a => s!"(Core.Term.inl {coreText label keys a})"
  | .inr a => s!"(Core.Term.inr {coreText label keys a})"
  | .sumCase a b c => s!"(Core.Term.sumCase {coreText label keys a} {coreText label keys b} {coreText label keys c})"
  | .pack declaration a => s!"(Core.Term.pack ({reprStr declaration}) {coreText label keys a})"
  | .unpack a => s!"(Core.Term.unpack {coreText label keys a})"

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
  | @Term.mapEmpty _ k _ => s!"{mapNamespace k}.empty"
  | @Term.setEmpty _ k => s!"{setNamespace k}.empty"
  | @Term.mapSet _ k _ m key value => s!"({mapNamespace k}.set {termText label keys m names depth} {termText label keys key names depth} {termText label keys value names depth})"
  | .inl a => s!"(_root_.Sum.inl {termText label keys a names depth})"
  | .inr a => s!"(_root_.Sum.inr {termText label keys a names depth})"
  | @Term.sumCase _ a b _ value left right =>
    let leftName := ident s!"_left#{depth}"
    let rightName := ident s!"_right#{depth}"
    s!"(_root_.Sum.elim (fun {leftName} : {typeText a} => {termText label keys left (leftName :: names) (depth + 1)}) (fun {rightName} : {typeText b} => {termText label keys right (rightName :: names) (depth + 1)}) {termText label keys value names depth})"
  | .pack declaration a => s!"(NativeConstruct.{ident declaration.name} {termText label keys a names depth})"
  | @Term.unpack _ declaration a => s!"(NativeDestruct.{ident declaration.name} {termText label keys a names depth})"

private def typeDeclarations : Core.Ty → List Named.Declaration
  | .named declaration => [declaration]
  | .option t | .list t | .map _ t => typeDeclarations t
  | .pair a b | .sum a b | .fn a b | .step a b | .exit a b => typeDeclarations a ++ typeDeclarations b
  | _ => []

private def termDeclarations (term : Term Γ t) : List Named.Declaration :=
  typeDeclarations t ++ match term with
  | .closed body => termDeclarations body
  | .unary _ a | .some a | .fst a | .snd a | .lam _ a | .next a | .stop a | .ret a |
      .inl a | .inr a | .pack _ a | .unpack a => termDeclarations a
  | .binary _ a b | .let_ _ a b | .cons a b | .pair a b | .app a b => termDeclarations a ++ termDeclarations b
  | .ite a b c | .optionCase a b c | .each a b c | .exitCase a b c | .mapSet a b c |
      .sumCase a b c | .listReduce a b c | .listSlice a b c =>
    termDeclarations a ++ termDeclarations b ++ termDeclarations c
  | .listMap a b | .listFilter a b | .listSome a b | .listEvery a b |
      .listFind a b | .listFindIndex a b => termDeclarations a ++ termDeclarations b
  | _ => []

private def nativeFieldNames (fields : List (String × Ariadne.Ty)) : List String :=
  let reserved := ["mk", "rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "brecOn", "below"]
  let names := fields.zipIdx.map fun ((name, _), i) =>
    if name.isEmpty || reserved.contains name || name.contains '»' || name.contains '\n' || name.contains '\r'
    then s!"field{i}" else name
  if names.eraseDups.length == names.length then names else
    fields.zipIdx.map fun (_, i) => s!"field{i}"

private def emitRecord (program : Program) (declaration : Named.Declaration) : Checked String := do
  let fields ← Declarations.record program declaration {}
  let names := nativeFieldNames fields
  let name := ident declaration.name
  let payloadType := typeText (Core.shapeType declaration.shape)
  let mut out := s!"structure NativeTypes.{name} where\n"
  let mut args : List String := []
  let mut payload : List String := []
  let mut pattern : List String := []
  for ((_field, source), i) in fields.zipIdx do
    if (Declarations.fixedString source).isSome then
      payload := payload ++ ["()"]
      pattern := pattern ++ ["⟨⟩"]
    else
      let fieldName := ident names[i]!
      let ty := Core.shapeType (← Declarations.shape {} 100 source)
      out := out ++ s!"  {fieldName} : {typeText ty}\n"
      args := args ++ ["(_payload" ++ String.join (List.replicate i ".2") ++ ".1)"]
      payload := payload ++ [s!"_value.{fieldName}"]
      pattern := pattern ++ [s!"_field{i}"]
  out := out ++ s!"\n@[simp] def NativeConstruct.{name} (_payload : {payloadType}) : NativeTypes.{name} :=\n" ++
    s!"  NativeTypes.{name}.mk" ++ String.join (args.map (" " ++ ·)) ++ "\n\n"
  let tuple := payload.foldr (fun value rest => s!"({value}, {rest})") "()"
  out := out ++ s!"@[simp] def NativeDestruct.{name} (_value : NativeTypes.{name}) : {payloadType} :=\n  {tuple}\n\n"
  let split := pattern.foldr (fun field rest => s!"⟨{field}, {rest}⟩") "⟨⟩"
  let data := (reprStr declaration).replace "\n" " "
  out := out ++ s!"def NativeRepresentations.{name} : Named.Representation (({data} : Named.Declaration).shape) where\n" ++
    s!"  Native := NativeTypes.{name}\n  construct := NativeConstruct.{name}\n  destruct := NativeDestruct.{name}\n" ++
    s!"  destruct_construct := by\n    intro value\n    rcases value with {split}\n    rfl\n" ++
    "  construct_destruct := by\n    intro value\n    cases value\n    rfl\n\n"
  return out

private def declarationOrder (program : Program) : Nat → Named.Declaration → Checked (List Named.Declaration)
  | 0, _ => Elaborate.refusal "A5101" "native declaration nesting budget exhausted" {}
  | n + 1, declaration => do
    if let some (left, right) ← Declarations.union program declaration {} then
      return (← declarationOrder program n left.declaration) ++
        (← declarationOrder program n right.declaration) ++ [declaration]
    return [declaration]

private def constructorName (source : Ariadne.Ty) (fallback : String) : String :=
  match Check.unreadonly source with
  | .record fields =>
    match fields.findSome? (fun (_, source) => Declarations.fixedString source) with
    | some tag =>
      let name := String.ofList (tag.map (fun unit => Char.ofNat unit.toNat))
      if !name.isEmpty && name.toList.all (fun c => c.isAlpha || c.isDigit || c == '_') &&
          !["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "below", "brecOn"].contains name
      then name else fallback
    | none => fallback
  | _ => fallback

private def emitDeclaration (program : Program) (declaration : Named.Declaration) : Checked String := do
  let some (left, right) ← Declarations.union program declaration {} | emitRecord program declaration
  let name := ident declaration.name
  let leftName := ident left.declaration.name
  let rightName := ident right.declaration.name
  let lc := constructorName left.source "left"
  let rc := constructorName right.source "right"
  let (lc, rc) := if lc == rc then ("left", "right") else (lc, rc)
  let lc := ident lc
  let rc := ident rc
  let payload := typeText (Core.shapeType declaration.shape)
  let data := (reprStr declaration).replace "\n" " "
  return s!"inductive NativeTypes.{name} where\n" ++
    s!"  | {lc} (value : NativeTypes.{leftName})\n  | {rc} (value : NativeTypes.{rightName})\n\n" ++
    s!"@[simp] def NativeConstruct.{name} (payload : {payload}) : NativeTypes.{name} :=\n" ++
    s!"  Sum.elim (fun value => .{lc} (NativeConstruct.{leftName} value))\n" ++
    s!"    (fun value => .{rc} (NativeConstruct.{rightName} value)) payload\n\n" ++
    s!"@[simp] def NativeDestruct.{name} (value : NativeTypes.{name}) : {payload} :=\n" ++
    s!"  match value with\n  | .{lc} value => .inl (NativeDestruct.{leftName} value)\n" ++
    s!"  | .{rc} value => .inr (NativeDestruct.{rightName} value)\n\n" ++
    s!"def NativeRepresentations.{name} : Named.Representation (({data} : Named.Declaration).shape) where\n" ++
    s!"  Native := NativeTypes.{name}\n  construct := NativeConstruct.{name}\n  destruct := NativeDestruct.{name}\n" ++
    "  destruct_construct := by\n    intro value\n    cases value with\n" ++
    s!"    | inl value => exact congrArg Sum.inl (NativeRepresentations.{leftName}.destruct_construct value)\n" ++
    s!"    | inr value => exact congrArg Sum.inr (NativeRepresentations.{rightName}.destruct_construct value)\n" ++
    "  construct_destruct := by\n    intro value\n    cases value with\n" ++
    s!"    | {lc} value => exact congrArg NativeTypes.{name}.{lc} (NativeRepresentations.{leftName}.construct_destruct value)\n" ++
    s!"    | {rc} value => exact congrArg NativeTypes.{name}.{rc} (NativeRepresentations.{rightName}.construct_destruct value)\n\n"

def emit (source : String) (program : Program) (namespace_ : String) : Checked String := do
  let original := program
  let program ← ClassPlan.lower program
  if program.functions.isEmpty then
    Elaborate.refusal "A5101" "there are no functions to extract" {}
  let compiled ← program.functions.mapM fun f => do return (f, ← Elaborate.function original f.name)
  let expanded ← Declarations.withVariants program
  let roots := (compiled.flatMap fun (_, core) =>
    core.params.flatMap typeDeclarations ++ termDeclarations core.body).eraseDups
  let declarations := (← roots.mapM (declarationOrder expanded 100)).flatten.eraseDups
  let mut out := (Ariadne.emit source original namespace_).replace
    "import Ariadne.Certificate\n" "import Ariadne.Certificate\nimport Ariadne.Shallow.Elaborate\nimport Ariadne.Shallow.Safety\n"
  out := out ++ "\n-- Shallow denotation certificates. Operational adequacy is not yet proved.\n" ++
    s!"namespace {namespace_}.Shallow\nopen Ariadne Ariadne.Shallow\nset_option linter.unusedSimpArgs false\n\n"
  let mut interpretation := "Named.canonical"
  for declaration in declarations do
    out := out ++ (← emitDeclaration expanded declaration)
    let data := (reprStr declaration).replace "\n" " "
    interpretation := s!"(Named.Interp.insert {interpretation} ({data}) NativeRepresentations.{ident declaration.name})"
  out := out ++ s!"def Interpretation.value : Named.Interp := {interpretation}\n\n" ++
    "theorem Interpretation.lawful : Named.Lawful Interpretation.value := Named.lawful _\n\n"
  for (f, core) in compiled do
    let coreName := "CoreArtifacts." ++ ident f.name
    let functionName := ident f.name
    let names := f.params.map (fun param => ident s!"_{param.name}#arg")
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
      out := out ++ s!"theorem JoinChecks.{j} : Denote.term (interp := Interpretation.value) JoinCore.{j} () = JoinNative.{j} := by\n" ++
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
    let safeEnv := names.foldr (fun name rest => s!"({name}, {rest})") "()"
    out := out ++ s!"abbrev {functionName}.safe{params} : Prop :=\n" ++
      s!"  Safety.function (interp := Interpretation.value) {coreName} (by decide) {safeEnv}\n\n"
    let envName := if core.params.isEmpty then "_env" else "env"
    let args := String.join ((List.range core.params.length).map fun i =>
      " (" ++ envName ++ String.join (List.replicate i ".2") ++ ".1)")
    out := out ++ s!"theorem {"DenotationChecks." ++ ident f.name} :\n" ++
      s!"    (fun {envName} : Core.Env {coreName}.params Interpretation.value => {functionName}{args}) =\n" ++
      s!"      Denote.function (interp := Interpretation.value) {coreName} := by\n" ++
      s!"  unfold {namespace_}.Shallow.{functionName}\n" ++
      s!"  simp only [Denote.function, {coreName}, Denote.term, Core.Var.get" ++
      String.join (checks.map (", " ++ ·)) ++ "] <;> rfl\n\n"
  return out ++ s!"end {namespace_}.Shallow\n"

end Ariadne.Shallow
