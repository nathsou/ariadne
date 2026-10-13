import Ariadne.Shallow.Safety
namespace Ariadne.Shallow.Safety

theorem each_value (body : α → σ → Step σ τ × Bool) (values : List α) (initial : σ) :
    (each body values initial).1 = Loop.each values initial (fun value state => (body value state).1) := by
  induction values generalizing initial with
  | nil => rfl
  | cons value rest ih =>
    cases called : body value initial with
    | mk step safe =>
      cases step <;> simp [each, Loop.each, called, ih]

theorem measured_value (measure : σ → Int × Bool) (body : σ → Step σ τ × Bool) (budget : Nat) (initial : σ) :
    (measured measure body budget initial).1 = Measured.iterate (fun state => (body state).1) budget initial := by
  induction budget generalizing initial with
  | zero => rfl
  | succ budget ih =>
    cases called : body initial with
    | mk step safe =>
      cases step <;> simp [measured, Measured.iterate, called, ih]

theorem foldl_value (body : σ → α → σ × Bool) (values : List α) (initial : σ) (safe : Bool) :
    (values.foldl (fun (state, safe) value =>
      let (state, step) := body state value
      (state, safe && step)) (initial, safe)).1 =
      values.foldl (fun state value => (body state value).1) initial := by
  induction values generalizing initial safe with
  | nil => rfl
  | cons value rest ih =>
    simpa only [List.foldl_cons] using ih (body initial value).1 (safe && (body initial value).2)

theorem search_value (predicate : α → Float.Model → Bool × Bool) (values : List α) (index : Nat) :
    (search predicate values index).1 =
      ((values.zipIdx index).find? (fun (value, index) => (predicate value (Float.Model.ofNat index)).1)).map
        (fun (value, index) => (index, value)) := by
  induction values generalizing index with
  | nil => rfl
  | cons value rest ih =>
    cases tested : predicate value (Float.Model.ofNat index) with
    | mk found safe =>
      cases found <;> simp [search, tested, List.zipIdx_cons, ih]

theorem search_some (predicate : α → Float.Model → Bool × Bool) (values : List α) :
    (search predicate values 0).1.isSome = JSArray.some (fun value index => (predicate value index).1) values := by
  rw [search_value]
  simp [JSArray.some, List.isSome_find?]

theorem search_find (predicate : α → Float.Model → Bool × Bool) (values : List α) :
    (search predicate values 0).1.map Prod.snd = JSArray.find (fun value index => (predicate value index).1) values := by
  rw [search_value]
  simp [JSArray.find, Option.map_map, Function.comp_def]

theorem search_every (predicate : α → Float.Model → Bool × Bool) (values : List α) :
    (search (fun value index => (!(predicate value index).1, (predicate value index).2)) values 0).1.isNone =
      JSArray.every (fun value index => (predicate value index).1) values := by
  rw [search_value]
  simp [JSArray.every, ← Option.not_isSome, List.isSome_find?, List.not_any_eq_all_not]

theorem map_value (body : α → Float.Model → β × Bool) (values : List α) :
    (values.mapIdx (fun index value => body value (Float.Model.ofNat index))).map Prod.fst =
      JSArray.map (fun value index => (body value index).1) values := by
  simp [JSArray.map, List.mapIdx_eq_zipIdx_map, List.map_map, Function.comp_def]

theorem filter_value (predicate : α → Float.Model → Bool × Bool) (values : List α) :
    ((values.mapIdx (fun index value => (value, predicate value (Float.Model.ofNat index)))).filter
      (fun result => result.2.1)).map Prod.fst =
      JSArray.filter (fun value index => (predicate value index).1) values := by
  simp [JSArray.filter, List.mapIdx_eq_zipIdx_map, List.filter_map, List.map_map, Function.comp_def]

private theorem find_index_zip (values : List α) (predicate : α × Nat → Bool) (start : Nat) :
    ((values.zipIdx start).find? predicate).map Prod.snd =
      ((values.zipIdx start).findIdx? predicate).map (· + start) := by
  induction values generalizing start with
  | nil => rfl
  | cons value rest ih =>
    by_cases found : predicate (value, start) = true
    · simp [List.zipIdx_cons, List.findIdx?_cons, found]
    · simp [List.zipIdx_cons, List.findIdx?_cons, found, ih, Option.map_map, Function.comp_def, Nat.add_comm, Nat.add_left_comm]

theorem search_index (predicate : α → Float.Model → Bool × Bool) (values : List α) :
    (search predicate values 0).1.map Prod.fst =
      values.zipIdx.findIdx? (fun (value, index) => (predicate value (Float.Model.ofNat index)).1) := by
  rw [search_value]
  simpa [Option.map_map, Function.comp_def] using find_index_zip values
    (fun (value, index) => (predicate value (Float.Model.ofNat index)).1) 0

theorem search_findIndex (predicate : α → Float.Model → Bool × Bool) (values : List α) :
    ((search predicate values 0).1.map (fun result => Float.Model.ofNat result.1)).getD (Float.Model.ofInt (-1)) =
      JSArray.findIndex (fun value index => (predicate value index).1) values := by
  have index := search_index predicate values
  have mapped := congrArg (Option.map Float.Model.ofNat) index
  simp only [Option.map_map, Function.comp_def] at mapped
  rw [mapped]
  unfold JSArray.findIndex
  cases values.zipIdx.findIdx? (fun (value, index) => (predicate value (Float.Model.ofNat index)).1) <;> rfl

end Ariadne.Shallow.Safety
