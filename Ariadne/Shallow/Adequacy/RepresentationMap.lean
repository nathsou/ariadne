import Ariadne.Shallow.Adequacy.ProjectionRecord
namespace Ariadne.Shallow.DataRelation
open Heap

theorem Elements.comap_iff {relation : DataRelation runtime α} {heap : Heap}
    {values : List runtime} {natives : List β} {footprint : Footprint} (decode : β → α) :
    Elements (relation.comap decode) heap values natives footprint ↔
      Elements relation heap values (natives.map decode) footprint := by
  constructor
  · intro related
    induction related with
    | nil => exact .nil
    | cons head tail separate ih => exact .cons head ih separate
  · intro related
    induction natives generalizing values footprint with
    | nil => cases related; exact .nil
    | cons native natives ih =>
      cases related with
      | cons head tail separate => exact .cons head (ih tail) separate

theorem array_comap_iff {relation : DataRelation Value α} {heap : Heap}
    {value : Value} {natives : List β} {footprint : Footprint} (decode : β → α) :
    (relation.comap decode).array.Holds heap value natives footprint ↔
      relation.array.Holds heap value (natives.map decode) footprint := by
  simp only [array, refine, reference, object, sequence, List.length_map]
  simp only [Elements.comap_iff]

end Ariadne.Shallow.DataRelation

namespace Ariadne.Shallow.JSArray

theorem get_map (decode : α → β) (xs : List α) (query : Float.Model) :
    get (xs.map decode) query = (get xs query).map decode := by
  cases converted : Ariadne.indexOf (.number query) <;>
    simp [get, converted, List.getElem?_map]

theorem map_decode (decode : β → γ) (update : α → Float.Model → β) (xs : List α) :
    (map update xs).map decode = map (fun item index => decode (update item index)) xs := by
  apply List.ext_getElem?
  intro index
  simp [map, List.getElem?_map, List.getElem?_mapIdx, Option.map_map, Function.comp_def]

end Ariadne.Shallow.JSArray

namespace Ariadne.Shallow.Adequacy
open Heap DataRelation

/-- Adapt the projection proof to a lawful named or structural native record.
Only constructor/destructor equations are required for the changed element. -/
theorem array_projection_decoded_record_update {codec : Value → α → Prop}
    {tail : DataRelation (List (String × Value)) β} {program : Program} {state : State}
    {outer : Nat} {natives : List γ} {owned : Footprint} {query : Float.Model}
    {before replacement : γ} {old updated : α} {rest : β}
    (decode : γ → α × β) (name op : String) (container keyExpr rhs : Expr) (delta value : Value)
    (indexSpan fieldSpan statementSpan : Span)
    (input : ((DataRelation.field name (DataRelation.scalar codec) tail).record.comap decode).array.Holds
      state.heap (.ref outer) natives owned)
    (found : JSArray.get natives query = some before)
    (decodedBefore : decode before = (old, rest)) (decodedUpdate : decode replacement = (updated, rest))
    (independent : IgnoresField tail name)
    (containerEval : Evaluates program state container (.ref outer) state)
    (keyEval : Evaluates program state keyExpr (.number query) state)
    (operandEval : Evaluates program state rhs delta state)
    (operation : ∀ before, codec before old → binary op before delta = .ok value)
    (encoded : codec value updated) :
    ∃ address after,
      ExecutesStatement program state
        (.update (.member (.index container keyExpr indexSpan) name fieldSpan) op rhs statementSpan) {state := after} ∧
      ((DataRelation.field name (DataRelation.scalar codec) tail).record.comap decode).array.Holds after.heap (.ref outer)
        (JSArray.map (fun item position => if position == query then replacement else item) natives) owned ∧
      Modifies [address] state.heap after.heap := by
  have mappedInput := (DataRelation.array_comap_iff decode).mp input
  have mappedFound : JSArray.get (natives.map decode) query = some (old, rest) := by
    simp only [JSArray.get_map, found, Option.map_some, decodedBefore]
  obtain ⟨address, after, executed, represented, writes⟩ := array_projection_record_update
    name op container keyExpr rhs delta value indexSpan fieldSpan statementSpan
    mappedInput mappedFound independent containerEval keyEval operandEval operation encoded
  have output :
      (JSArray.map (fun item position => if position == query then replacement else item) natives).map decode =
        JSArray.map (fun item position => if position == query then (updated, rest) else item) (natives.map decode) := by
    apply List.ext_getElem?
    intro i
    cases foundItem : natives[i]? with
    | none => simp [JSArray.map, List.getElem?_mapIdx, List.getElem?_map, foundItem]
    | some item =>
      simp only [JSArray.map, List.getElem?_mapIdx, List.getElem?_map, foundItem, Option.map_some]
      split <;> simp_all
  refine ⟨address, after, executed, (DataRelation.array_comap_iff decode).mpr ?_, writes⟩
  rw [output]
  exact represented
end Ariadne.Shallow.Adequacy
