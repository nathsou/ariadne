import Ariadne.Shallow.Adequacy.Function
import Ariadne.Shallow.Adequacy.Optional
import Ariadne.Shallow.Adequacy.Record
import Ariadne.Shallow.SourceData

namespace Ariadne.Shallow.Adequacy
open Core Heap DataRelation

abbrev Layouts (Γ : List Core.Ty) (interp : Named.Interp) :=
  ∀ {t}, Var Γ t → DataRelation Value (t.denote interp)

structure ReadEnvironment {interp : Named.Interp} (names : Names Γ) (layouts : Layouts Γ interp)
    (state : State) (env : Core.Env Γ interp) : Prop where
  scalar : Environment names state env
  data : ∀ {t} (v : Var Γ t), names.visible v = true →
    ∃ value footprint, state.lookup (names.get v) = .ok value ∧
      (layouts v).Holds state.heap value (v.get env) footprint

def Scalar.layout {interp : Named.Interp} (scalar : Scalar t) : DataRelation Value (t.denote interp) :=
  DataRelation.scalar (fun value native => value = scalar.encode native)

/-- Read certificates connect source expressions to their actual typed Core
terms and runtime layouts. Field premises describe a local projection; they
do not assume evaluation of a source expression or function. -/
inductive ReadExpr {interp : Named.Interp} {Γ : List Core.Ty} (names : Names Γ)
    (layouts : Layouts Γ interp) : {t : Core.Ty} →
    DataRelation Value (t.denote interp) → Expr → Term Γ t → Prop where
  | scalar {scalar : Scalar t} {expression : Expr} {term : Term Γ t}
      (input : ScalarExpr names scalar expression term) :
      ReadExpr (interp := interp) names (@layouts) (t := t) scalar.layout expression term
  | var (v : Var Γ t) (visible : names.visible v = true) (span : Span) :
      ReadExpr (interp := interp) names (@layouts) (t := t) (layouts v) (.var (names.get v) span) (.var v)
  | arrayLength {element : DataRelation Value (t.denote interp)} {expression : Expr}
      {value : Term Γ (.list t)} (input : ReadExpr (interp := interp) names (@layouts) (t := .list t) element.array expression value) (span : Span) :
      ReadExpr (interp := interp) names (@layouts) (t := .number) Scalar.number.layout (.member expression "length" span) (.unary .length value)
  | arrayLengthInt53 {element : DataRelation Value (t.denote interp)} {expression : Expr}
      {value : Term Γ (.list t)} (input : ReadExpr (interp := interp) names (@layouts) (t := .list t) element.array expression value) (span : Span) :
      ReadExpr (interp := interp) names (@layouts) (t := .int53) Scalar.int53.layout (.member expression "length" span) (.unary .lengthInt53 value)
  | arrayGet {element : DataRelation Value (t.denote interp)} {expression index : Expr}
      {value : Term Γ (.list t)} {position : Term Γ .number}
      (input : ReadExpr (interp := interp) names (@layouts) (t := .list t) element.array expression value)
      (query : ScalarExpr names .number index position) (span : Span) :
      ReadExpr (interp := interp) names (@layouts) (t := .option t) element.option (.index expression index span) (.binary .get value position)
  | arrayGetOptional {element : DataRelation Value (t.denote interp)} {expression index : Expr}
      {value : Term Γ (.list (.option t))} {position : Term Γ .number}
      (input : ReadExpr (interp := interp) names (@layouts) (t := .list (.option t)) element.option.array expression value)
      (query : ScalarExpr names .number index position) (span : Span) :
      ReadExpr (interp := interp) names (@layouts) (t := .option t) element.option (.index expression index span)
        (.optionCase (.binary .get value position) .none (.var .here))
  | field {record : DataRelation (List (String × Value)) (a.denote interp)}
      {element : DataRelation Value (b.denote interp)} {expression : Expr}
      {value : Term Γ a} {result : Term Γ b} {get : a.denote interp → b.denote interp}
      (input : ReadExpr (interp := interp) names (@layouts) (t := a) record.record expression value)
      (name : String) (field : ReadsField record name element get)
      (projection : ∀ env : Core.Env Γ interp, Denote.term result env = get (Denote.term value env))
      (span : Span) : ReadExpr (interp := interp) names (@layouts) (t := b) element (.member expression name span) result

theorem ReadExpr.sound {interp : Named.Interp} {names : Names Γ} {layouts : Layouts Γ interp}
    {layout : DataRelation Value (t.denote interp)} {expression : Expr} {term : Term Γ t}
    (translation : ReadExpr names (@layouts) layout expression term) (program : Program)
    (state : State) (env : Core.Env Γ interp) (inputs : ReadEnvironment names (@layouts) state env) :
    ∃ value footprint, Evaluates program state expression value state ∧
      layout.Holds state.heap value (Denote.term term env) footprint := by
  induction translation with
  | scalar input =>
    exact ⟨_, [], input.sound program interp state env inputs.scalar, rfl, rfl⟩
  | var v visible span =>
    obtain ⟨value, footprint, lookup, related⟩ := inputs.data v visible
    exact ⟨value, footprint, Evaluates.variable program state _ span value
      (State.lookup_present lookup) lookup, related⟩
  | arrayLength input span ih =>
    obtain ⟨value, footprint, evaluated, related⟩ := ih
    exact ⟨_, [], evaluated.member "length" span (array_length related), rfl, rfl⟩
  | arrayLengthInt53 input span ih =>
    obtain ⟨value, footprint, evaluated, related⟩ := ih
    exact ⟨_, [], evaluated.member "length" span (array_length related), rfl, rfl⟩
  | @arrayGet t element expression index value position input query span ih =>
    obtain ⟨value, footprint, evaluated, related⟩ := ih
    obtain ⟨result, borrowed, read, _, found⟩ := array_get related (Denote.term position env)
    exact ⟨result, borrowed, evaluated.index (query.sound program interp state env inputs.scalar) span read, found⟩
  | @arrayGetOptional t element expression index value position input query span ih =>
    obtain ⟨runtime, footprint, evaluated, related⟩ := ih
    obtain ⟨result, borrowed, read, _, found⟩ := array_get_optional related (Denote.term position env)
    refine ⟨result, borrowed, evaluated.index (query.sound program interp state env inputs.scalar) span read, ?_⟩
    change element.option.Holds state.heap result
      ((JSArray.get (Denote.term value env) (Denote.term position env)).elim none id) borrowed
    cases fetched : JSArray.get (Denote.term value env) (Denote.term position env) <;>
      simpa only [fetched, Option.join, Option.bind, Option.elim, id] using found
  | field input name field projection span ih =>
    obtain ⟨value, footprint, evaluated, related⟩ := ih
    obtain ⟨result, borrowed, read, _, found⟩ := record_get related field
    exact ⟨result, borrowed, evaluated.member name span read, projection env ▸ found⟩

theorem read_expression_source {source : String} (certificate : Certificate source)
    (function : Ariadne.Function) (names : Names Γ) (layouts : Layouts Γ interp)
    (layout : DataRelation Value (t.denote interp)) (term : Term Γ t)
    (expression : Expr) (returnSpan blockSpan : Span)
    (lookup : certificate.program.functions.find? (fun f => f.name == function.name) = some function)
    (body : function.body = .block [.return_ expression returnSpan] blockSpan)
    (translation : ReadExpr names (@layouts) layout expression term)
    (env : Core.Env Γ interp) (heap : Heap) (args : List Value)
    (inputs : ReadEnvironment names (@layouts) (bindArguments {heap} function.params args) env) :
    SourceRepresentsFrom source function.name heap args layout (Denote.term term env) := by
  obtain ⟨value, footprint, evaluated, related⟩ := translation.sound certificate.program _ env inputs
  exact transfer_represented certificate (invoke_return lookup body evaluated) related

end Ariadne.Shallow.Adequacy
