import Ariadne.Shallow.Safety.Erasure

namespace Ariadne.Shallow.Safety
open Core

private theorem castOption {α β : Type} (equal : α = β) (types : Option α = Option β) (x : Option α) :
    cast types x = x.map (cast equal) := by
  cases equal
  change x = x.map id
  cases x <;> rfl

private theorem castList {α β : Type} (equal : α = β) (types : List α = List β) (x : List α) :
    cast types x = x.map (cast equal) := by
  cases equal
  change x = x.map id
  simp

private theorem castPair {α β γ δ : Type} (left : α = γ) (right : β = δ)
    (types : (α × β) = (γ × δ)) (x : α × β) : cast types x = (cast left x.1, cast right x.2) := by
  cases left; cases right
  simp

private theorem castSum {α β γ δ : Type} (left : α = γ) (right : β = δ)
    (types : Sum α β = Sum γ δ) (x : Sum α β) : cast types x = x.map (cast left) (cast right) := by
  cases left; cases right
  cases x <;> rfl

private theorem castMapEntries {κ α β : Type} [eqκ : BEq κ] (equal : α = β)
    (types : JSMap κ α = JSMap κ β) (x : JSMap κ α) :
    (cast types x).entries = x.entries.map (fun (key, value) => (key, cast equal value)) := by
  cases equal
  simp

private theorem mapLeft (values : List α) (f : α → β) (relation : β → α → Prop)
    (step : ∀ x, relation (f x) x) : ListRelated relation (values.map f) values := by
  induction values with
  | nil => exact .nil
  | cons x xs ih => exact .cons (step x) ih

/-- Native data lift preserves the higher-order erasure relation. -/
theorem erases_cast {interp : Named.Interp} (t : Core.Ty) (data : dataType t = true) (value : t.denote interp) :
    Erases t (cast (data_model t interp data).symm value) value := by
  induction t with
  | unit | bool | int | int53 | number | string | named => simp only [cast_eq, Erases]
  | option a ih =>
    have ha : dataType a = true := data
    rw [castOption (data_model a interp ha).symm]
    cases value with
    | none => trivial
    | some value => exact ih ha value
  | list a ih =>
    have ha : dataType a = true := data
    rw [castList (data_model a interp ha).symm]
    induction value with
    | nil => exact .nil
    | cons value values rest => exact .cons (ih ha value) rest
  | map k a ih =>
    have ha : dataType a = true := data
    cases k <;> simp only [Erases, NumberMap.entries]
    all_goals
      first
      | rw [castMapEntries (eqκ := NumberKey.equality) (data_model a interp ha).symm]
      | rw [castMapEntries (data_model a interp ha).symm]
      apply mapLeft
      intro entry
      cases entry
      exact ⟨rfl, ih ha _⟩
  | set k => simp only [cast_eq, Erases]
  | pair a b iha ihb =>
    have parts : dataType a = true ∧ dataType b = true := by simpa only [dataType, Bool.and_eq_true] using data
    rw [castPair (data_model a interp parts.1).symm (data_model b interp parts.2).symm]
    exact ⟨iha parts.1 value.1, ihb parts.2 value.2⟩
  | sum a b iha ihb =>
    have parts : dataType a = true ∧ dataType b = true := by simpa only [dataType, Bool.and_eq_true] using data
    rw [castSum (data_model a interp parts.1).symm (data_model b interp parts.2).symm]
    cases value with
    | inl value => exact iha parts.1 value
    | inr value => exact ihb parts.2 value
  | fn | step | exit => simp [dataType] at data

private theorem mapEq [eqκ : BEq κ] {a b : JSMap κ α} (entries : a.entries = b.entries) : a = b := by
  cases a; cases b; cases entries; rfl

theorem erases_data_eq {interp : Named.Interp} (t : Core.Ty) (data : dataType t = true)
    (model : Model t interp) (native : t.denote interp) (related : Erases t model native) :
    cast (data_model t interp data) model = native := by
  induction t with
  | unit | bool | int | int53 | number | string | named | set =>
    simpa only [cast_eq, Erases] using related
  | option a ih =>
    have ha : dataType a = true := data
    rw [castOption (data_model a interp ha)]
    cases model <;> cases native <;> simp only [Erases, OptionRelated] at related
    · rfl
    · exact congrArg some (ih ha _ _ related)
  | list a ih =>
    have ha : dataType a = true := data
    rw [castList (data_model a interp ha)]
    exact ((related.map (cast (data_model a interp ha)) id
      (result := Eq) (fun _ _ h => ih ha _ _ h)).eq).trans (by simp)
  | map k a ih =>
    have ha : dataType a = true := data
    cases k
    all_goals first | apply mapEq (eqκ := NumberKey.equality) | apply mapEq
    all_goals
      first
      | rw [castMapEntries (eqκ := NumberKey.equality) (data_model a interp ha)]
      | rw [castMapEntries (data_model a interp ha)]
      have mapped := related.map (fun (key, value) => (key, cast (data_model a interp ha) value)) id
        (result := Eq) (fun x y h => Prod.ext h.1 (ih ha _ _ h.2))
      simpa only [List.map_id, NumberMap.entries] using mapped.eq
  | pair a b iha ihb =>
    have parts : dataType a = true ∧ dataType b = true := by simpa only [dataType, Bool.and_eq_true] using data
    rw [castPair (data_model a interp parts.1) (data_model b interp parts.2)]
    exact Prod.ext (iha parts.1 _ _ related.1) (ihb parts.2 _ _ related.2)
  | sum a b iha ihb =>
    have parts : dataType a = true ∧ dataType b = true := by simpa only [dataType, Bool.and_eq_true] using data
    rw [castSum (data_model a interp parts.1) (data_model b interp parts.2)]
    cases model <;> cases native <;> simp only [Erases] at related
    · exact congrArg Sum.inl (iha parts.1 _ _ related)
    · exact congrArg Sum.inr (ihb parts.2 _ _ related)
  | fn | step | exit => simp [dataType] at data

theorem ErasesEnvironment.lift {interp : Named.Interp} (types : List Core.Ty)
    (data : types.all dataType = true) (native : Core.Env types interp) :
    ErasesEnvironment (liftEnvironment types data native) native := by
  induction types with
  | nil => intro t v; cases v
  | cons t types ih =>
    have parts : dataType t = true ∧ types.all dataType = true := by simpa only [List.all_cons, Bool.and_eq_true] using data
    intro u v
    cases v with
    | here => exact erases_cast t parts.1 native.1
    | there v => exact ih parts.2 native.2 v

theorem shape_data (shape : Named.Shape) : dataType (shapeType shape) = true := by
  induction shape <;> simp_all [shapeType, dataType]

private theorem castCompose {α β γ : Type} (ab : α = β) (bc : β = γ) (ac : α = γ) (x : α) :
    cast bc (cast ab x) = cast ac x := by
  cases ab; cases bc; rfl

theorem erases_shape_eq {interp : Named.Interp} (shape : Named.Shape)
    (model : Model (shapeType shape) interp) (native : (shapeType shape).denote interp)
    (related : Erases (shapeType shape) model native) :
    cast (shape_model shape interp) model = cast (shape_denote shape interp) native := by
  have equal := congrArg (cast (shape_denote shape interp)) (erases_data_eq _ (shape_data shape) model native related)
  rw [castCompose (data_model _ interp (shape_data shape)) (shape_denote shape interp) (shape_model shape interp)] at equal
  exact equal

theorem erases_shape_of_eq {interp : Named.Interp} (shape : Named.Shape)
    (model : Model (shapeType shape) interp) (native : (shapeType shape).denote interp)
    (equal : cast (shape_model shape interp) model = cast (shape_denote shape interp) native) :
    Erases (shapeType shape) model native := by
  have corresponding : cast (data_model _ interp (shape_data shape)) model = native := by
    have back := congrArg (cast (shape_denote shape interp).symm) equal
    rw [castCompose _ _ (data_model _ interp (shape_data shape))] at back
    simpa only [cast_cast, cast_eq] using back
  have lifted := erases_cast _ (shape_data shape) native
  have roundTrip : cast (data_model _ interp (shape_data shape)).symm native = model := by
    rw [← corresponding]
    simp
  simpa only [roundTrip] using lifted

end Ariadne.Shallow.Safety
