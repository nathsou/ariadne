import Ariadne.Shallow.Adequacy.WPHeap
import Ariadne.Shallow.Adequacy.ScalarMap

/-!
Weakest-precondition rules for the array builtins that take callbacks, and
traversal laws for callbacks whose calls only append to the heap. A callback
specification names the value each call returns; the traversal laws then give
the builtin's result as the native list operation applied to that function.
Representation lemmas turn arrays of scalars into concrete heap facts.
-/

namespace Ariadne

def WPReduce (program : Program) (state : State) (callback : Value) (values : List Value) (acc : Value)
    (index : Nat) (post : Value → State → Prop) : Prop :=
  ∃ result after, Converges (fun fuel => reduce program fuel state callback values acc index)
    (.ok (result, after)) ∧ post result after

def WPSearch (program : Program) (state : State) (callback : Value) (values : List Value) (index : Nat)
    (mode : String) (post : Value → State → Prop) : Prop :=
  ∃ result after, Converges (fun fuel => search program fuel state callback values index mode)
    (.ok (result, after)) ∧ post result after

theorem WPTraverse.mono' {program : Program} {state : State} {callback : Value} {values : List Value}
    {index : Nat} {mode : String} {p q : List Value → State → Prop}
    (h : WPTraverse program state callback values index mode p) (f : ∀ results after, p results after → q results after) :
    WPTraverse program state callback values index mode q :=
  h.mono f

theorem WPReduce.mono {program : Program} {state : State} {callback : Value} {values : List Value}
    {acc : Value} {index : Nat} {p q : Value → State → Prop}
    (h : WPReduce program state callback values acc index p) (f : ∀ v s, p v s → q v s) :
    WPReduce program state callback values acc index q := by
  obtain ⟨v, s, e, hp⟩ := h
  exact ⟨v, s, e, f v s hp⟩

theorem WPSearch.mono {program : Program} {state : State} {callback : Value} {values : List Value}
    {index : Nat} {mode : String} {p q : Value → State → Prop}
    (h : WPSearch program state callback values index mode p) (f : ∀ v s, p v s → q v s) :
    WPSearch program state callback values index mode q := by
  obtain ⟨v, s, e, hp⟩ := h
  exact ⟨v, s, e, f v s hp⟩

/-! ## Builtins -/

theorem WPI.array_map {program : Program} {state : State} {post : Value → State → Prop}
    {address : Nat} {values : List Value} {callback : Value}
    (lookup : state.heap[address]? = some (.array values))
    (h : WPTraverse program state callback values 0 "map" (fun results after =>
      post (.ref after.heap.length) (after.alloc (.array results)).2)) :
    WPI program state (.method address "map") [callback] post := by
  unfold WPTraverse at h; unfold WPI
  obtain ⟨results, after, ⟨_, fuel, traversed⟩, q⟩ := h
  refine ⟨_, _, ⟨(by intro h; cases h), fuel + 1, ?_⟩, q⟩
  simp [apply, lookup, traversed, State.alloc, bind, Except.bind, pure, Except.pure]

theorem WPI.array_reduce {program : Program} {state : State} {post : Value → State → Prop}
    {address : Nat} {values : List Value} {callback initial : Value}
    (lookup : state.heap[address]? = some (.array values))
    (h : WPReduce program state callback values initial 0 post) :
    WPI program state (.method address "reduce") [callback, initial] post := by
  unfold WPI
  obtain ⟨result, after, ⟨_, fuel, reduced⟩, q⟩ := h
  refine ⟨_, _, ⟨(by intro h; cases h), fuel + 1, ?_⟩, q⟩
  simp [apply, lookup, reduced]

theorem WPI.array_search {program : Program} {state : State} {post : Value → State → Prop}
    {address : Nat} {values : List Value} {callback : Value} {mode : String}
    (supported : mode = "some" ∨ mode = "every" ∨ mode = "find" ∨ mode = "findIndex")
    (lookup : state.heap[address]? = some (.array values))
    (h : WPSearch program state callback values 0 mode post) :
    WPI program state (.method address mode) [callback] post := by
  unfold WPI
  obtain ⟨result, after, ⟨_, fuel, searched⟩, q⟩ := h
  refine ⟨_, _, ⟨(by intro h; cases h), fuel + 1, ?_⟩, q⟩
  rcases supported with rfl | rfl | rfl | rfl <;> simp [apply, lookup, searched]

theorem WPI.array_toReversed {program : Program} {state : State} {post : Value → State → Prop}
    {address : Nat} {values : List Value}
    (lookup : state.heap[address]? = some (.array values))
    (h : post (.ref state.heap.length) (state.alloc (.array values.reverse)).2) :
    WPI program state (.method address "toReversed") [] post := by
  unfold WPI
  exact ⟨_, _, ⟨(by intro h; cases h), 1, by simp [apply, lookup, State.alloc, pure, Except.pure]⟩, h⟩

theorem WPReduce.nil {program : Program} {state : State} {callback acc : Value} {index : Nat}
    {post : Value → State → Prop} (h : post acc state) : WPReduce program state callback [] acc index post :=
  ⟨acc, state, ⟨(by intro h; cases h), 1, by simp [reduce, pure, Except.pure]⟩, h⟩

theorem WPReduce.cons {program : Program} {state : State} {callback acc x : Value} {xs : List Value}
    {index : Nat} {post : Value → State → Prop}
    (h : WPI program state callback [acc, x, .number (Float.Model.ofNat index)] (fun acc' middle =>
      WPReduce program middle callback xs acc' (index + 1) post)) :
    WPReduce program state callback (x :: xs) acc index post := by
  unfold WPI at h
  obtain ⟨acc', middle, ⟨_, ni, invoked⟩, result, after, ⟨_, nr, reduced⟩, q⟩ := h
  obtain ⟨ti, hi⟩ := ((converges_iff_eventually _ (fun h => apply_fuel_mono program h state callback _) _).mp
    ⟨(by intro h; cases h), ni, invoked⟩).2
  obtain ⟨tr, hr⟩ := ((converges_iff_eventually _
    (fun h => reduce_fuel_mono program h middle callback xs acc' (index + 1)) _).mp
    ⟨(by intro h; cases h), nr, reduced⟩).2
  refine ⟨result, after, ⟨(by intro h; cases h), max ti tr + 1, ?_⟩, q⟩
  simp [reduce, hi _ (Nat.le_max_left ..), hr _ (Nat.le_max_right ..), bind, Except.bind]

theorem WPSearch.nil {program : Program} {state : State} {callback : Value} {index : Nat} {mode : String}
    {post : Value → State → Prop}
    (h : post (if mode == "find" then .undefined else if mode == "findIndex" then
      .number (Float.Model.ofInt (-1)) else .boolean (mode == "every")) state) :
    WPSearch program state callback [] index mode post :=
  ⟨_, state, ⟨(by intro h; cases h), 1, by simp [search, pure, Except.pure]⟩, h⟩

theorem WPSearch.cons {program : Program} {state : State} {callback x : Value} {xs : List Value}
    {index : Nat} {mode : String} {post : Value → State → Prop}
    (h : WPI program state callback [x, .number (Float.Model.ofNat index)] (fun answer middle =>
      if answer.truthy != (mode == "every") then
        post (if mode == "find" then x else if mode == "findIndex" then
          .number (Float.Model.ofNat index) else .boolean (mode != "every")) middle
      else WPSearch program middle callback xs (index + 1) mode post)) :
    WPSearch program state callback (x :: xs) index mode post := by
  unfold WPI at h
  obtain ⟨answer, middle, ⟨_, ni, invoked⟩, q⟩ := h
  obtain ⟨ti, hi⟩ := ((converges_iff_eventually _ (fun h => apply_fuel_mono program h state callback _) _).mp
    ⟨(by intro h; cases h), ni, invoked⟩).2
  by_cases stop : (answer.truthy != (mode == "every")) = true
  · simp only [stop, ↓reduceIte] at q
    refine ⟨_, middle, ⟨(by intro h; cases h), ti + 1, ?_⟩, q⟩
    simp [search, hi _ (Nat.le_refl _), stop, bind, Except.bind, pure, Except.pure]
  · simp only [stop, Bool.false_eq_true, ↓reduceIte] at q
    obtain ⟨result, after, ⟨_, ns, searched⟩, q⟩ := q
    obtain ⟨ts, hs⟩ := ((converges_iff_eventually _
      (fun h => search_fuel_mono program h middle callback xs (index + 1) mode) _).mp
      ⟨(by intro h; cases h), ns, searched⟩).2
    refine ⟨result, after, ⟨(by intro h; cases h), max ti ts + 1, ?_⟩, q⟩
    have stop' : (answer.truthy != (mode == "every")) = false := by simpa using stop
    simp [search, hi _ (Nat.le_max_left ..), hs _ (Nat.le_max_right ..), stop', bind, Except.bind]

/-! ## Callbacks that only append to the heap -/

/-- The heap prefix `base` is unchanged. -/
def Frames (base : Heap) (state : State) : Prop := ∀ j, j < base.length → state.heap[j]? = base[j]?

theorem Frames.refl (state : State) : Frames state.heap state := fun _ _ => rfl

/-- The object allocated last before `base` was taken is still there. -/
theorem Frames.alloc_lookup {s state : State} {o : Object} (frames : Frames (s.alloc o).2.heap state) :
    state.heap[s.heap.length]? = some o := by
  rw [frames _ (by simp [State.alloc])]
  simp [State.alloc]

theorem Frames.lookup {base : Heap} {state : State} {i : Nat} {o : Object} (frames : Frames base state)
    (h : base[i]? = some o) : state.heap[i]? = some o :=
  (frames i (bound_of_some h)).trans h

/-- Frames compose: a state that keeps a later heap keeps every prefix it kept. -/
theorem Frames.trans {a b : Heap} {state : State} (ab : ∀ j, j < a.length → b[j]? = a[j]?)
    (bc : Frames b state) : Frames a state := by
  intro j hj
  have := length_le_of_agree ab
  rw [bc j (by omega)]
  exact ab j hj

theorem Frames.heap_eq {base : Heap} {s t : State} (frames : Frames base s) (same : t.heap = s.heap) :
    Frames base t := by
  intro j hj; rw [same]; exact frames j hj

theorem Frames.append {base : Heap} {state : State} (frames : Frames base state) (extra : List Object)
    (env : Env) : Frames base { env := env, heap := state.heap ++ extra } := by
  intro j hj
  have := length_le_of_agree frames
  simp only
  rw [List.getElem?_append_left (by omega)]
  exact frames j hj

/-- The invariant a callback call keeps: the function's heap prefix, and the
closure itself. -/
structure Kept (base : Heap) (closure : Nat) (object : Object) (state : State) : Prop where
  frames : Frames base state
  lookup : state.heap[closure]? = some object

theorem Kept.append {base : Heap} {closure : Nat} {object : Object} {state : State}
    (kept : Kept base closure object state) (extra : List Object) (env : Env) :
    Kept base closure object { env := env, heap := state.heap ++ extra } :=
  ⟨kept.frames.append extra env, by rw [List.getElem?_append_left (bound_of_some kept.lookup)]; exact kept.lookup⟩

theorem Kept.heap_eq {base : Heap} {closure : Nat} {object : Object} {s t : State}
    (kept : Kept base closure object s) (same : t.heap = s.heap) : Kept base closure object t :=
  ⟨kept.frames.heap_eq same, by rw [same]; exact kept.lookup⟩

/-- A traversal starting right after the closure's allocation keeps the invariant. -/
theorem Kept.start {base : Heap} {s : State} {object : Object} (frames : Frames base s) :
    Kept base s.heap.length object (s.alloc object).2 :=
  ⟨by
    intro j hj
    have := length_le_of_agree frames
    simp only [State.alloc]
    rw [List.getElem?_append_left (by omega)]
    exact frames j hj, by simp [State.alloc]⟩

theorem Frames.alloc {base : Heap} {s : State} (frames : Frames base s) (object : Object) :
    Frames base (s.alloc object).2 := by
  intro j hj
  have := length_le_of_agree frames
  simp only [State.alloc]
  rw [List.getElem?_append_left (by omega)]
  exact frames j hj

theorem Frames.bindArguments (s : State) (params : List Param) (args : List Value) :
    Frames s.heap (Shallow.Adequacy.bindArguments s params args) := by
  unfold Shallow.Adequacy.bindArguments
  generalize hs : ({ s with env := [] } : State) = start
  have same : start.heap = s.heap := by rw [← hs]
  rw [← same]
  clear hs same
  induction params generalizing args start with
  | nil => intro j _; simp
  | cons p ps ih =>
    cases args with
    | nil => intro j _; simp
    | cons v vs =>
      intro j hj
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih vs (start.declare p.name v) j (by simp [State.declare, State.alloc]; omega)]
      simp [State.declare, State.alloc, List.getElem?_append_left hj]

/-- Every call on an element of `domain` from a state satisfying `inv` returns
`f` of that element, keeps `inv` and restores the caller's bindings. -/
def Callback (program : Program) (inv : State → Prop) (callback : Value) (domain : List Value)
    (f : Value → Value) : Prop :=
  ∀ state x (index : Nat), x ∈ domain → inv state →
    WPI program state callback [x, .number (Float.Model.ofNat index)] (fun result after =>
      result = f x ∧ inv after ∧ after.env = state.env)

/-- Two-argument callbacks for `reduce`: the accumulator and the element. -/
def Reducer (program : Program) (inv : State → Prop) (callback : Value) (domain : List Value)
    (f : Value → Value → Value) : Prop :=
  ∀ state acc x (index : Nat), x ∈ domain → inv state →
    WPI program state callback [acc, x, .number (Float.Model.ofNat index)] (fun result after =>
      result = f acc x ∧ inv after ∧ after.env = state.env)

theorem traverse_callback {program : Program} {inv : State → Prop} {callback : Value} {domain : List Value}
    {f : Value → Value} (spec : Callback program inv callback domain f) (mode : String) :
    ∀ (xs : List Value) (state : State) (index : Nat), (∀ x ∈ xs, x ∈ domain) → inv state →
      WPTraverse program state callback xs index mode (fun results after =>
        results = (if mode == "filter" then xs.filter (fun x => (f x).truthy) else xs.map f) ∧
        inv after ∧ after.env = state.env) := by
  intro xs
  induction xs with
  | nil => intro state index _ held; exact WPTraverse.nil ⟨by split <;> rfl, held, rfl⟩
  | cons x xs ih =>
    intro state index sub held
    refine WPTraverse.cons ((spec state x index (sub x (by simp)) held).mono ?_)
    rintro y middle ⟨rfl, held', env'⟩
    refine (ih middle (index + 1) (fun x member => sub x (by simp [member])) held').mono ?_
    rintro ys after ⟨rfl, held'', env''⟩
    refine ⟨?_, held'', env''.trans env'⟩
    by_cases filter : (mode == "filter") = true
    · simp only [filter, ↓reduceIte, List.filter_cons]
      try (split <;> simp_all)
    · simp [filter]

theorem reduce_callback {program : Program} {inv : State → Prop} {callback : Value} {domain : List Value}
    {f : Value → Value → Value} (spec : Reducer program inv callback domain f) :
    ∀ (xs : List Value) (state : State) (acc : Value) (index : Nat), (∀ x ∈ xs, x ∈ domain) → inv state →
      WPReduce program state callback xs acc index (fun result after =>
        result = xs.foldl f acc ∧ inv after ∧ after.env = state.env) := by
  intro xs
  induction xs with
  | nil => intro state acc index _ held; exact WPReduce.nil ⟨rfl, held, rfl⟩
  | cons x xs ih =>
    intro state acc index sub held
    refine WPReduce.cons ((spec state acc x index (sub x (by simp)) held).mono ?_)
    rintro y middle ⟨rfl, held', env'⟩
    refine (ih middle _ (index + 1) (fun x member => sub x (by simp [member])) held').mono ?_
    rintro result after ⟨rfl, held'', env''⟩
    exact ⟨rfl, held'', env''.trans env'⟩

/-- `find`, `some` and `every` with a callback specification. -/
def searchResult (f : Value → Value) (mode : String) : List Value → Value
  | [] => if mode == "find" then .undefined else .boolean (mode == "every")
  | x :: xs => if (f x).truthy != (mode == "every") then
      (if mode == "find" then x else .boolean (mode != "every")) else searchResult f mode xs

theorem search_callback {program : Program} {inv : State → Prop} {callback : Value} {domain : List Value}
    {f : Value → Value} (spec : Callback program inv callback domain f) (mode : String)
    (supported : mode = "some" ∨ mode = "every" ∨ mode = "find") :
    ∀ (xs : List Value) (state : State) (index : Nat), (∀ x ∈ xs, x ∈ domain) → inv state →
      WPSearch program state callback xs index mode (fun result after =>
        result = searchResult f mode xs ∧ inv after ∧ after.env = state.env) := by
  have notIndex : (mode == "findIndex") = false := by rcases supported with rfl | rfl | rfl <;> rfl
  intro xs
  induction xs with
  | nil =>
    intro state index _ held
    exact WPSearch.nil ⟨by simp [searchResult, notIndex], held, rfl⟩
  | cons x xs ih =>
    intro state index sub held
    refine WPSearch.cons ((spec state x index (sub x (by simp)) held).mono ?_)
    rintro y middle ⟨rfl, held', env'⟩
    by_cases stop : ((f x).truthy != (mode == "every")) = true
    · simp only [stop, ↓reduceIte, notIndex, Bool.false_eq_true]
      exact ⟨by simp [searchResult, stop], held', env'⟩
    · simp only [stop, Bool.false_eq_true, ↓reduceIte]
      refine (ih middle (index + 1) (fun x member => sub x (by simp [member])) held').mono ?_
      rintro result after ⟨rfl, held'', env''⟩
      exact ⟨by simp [searchResult, stop], held'', env''.trans env'⟩

/-! ## Callbacks specified by native functions -/

/-- Every call on an encoded native element returns the encoding of `g` of it. -/
def NativeCallback (program : Program) (inv : State → Prop) (callback : Value) (encode : κ → Value)
    (out : μ → Value) (g : κ → μ) : Prop :=
  ∀ state (n : κ) (index : Nat), inv state →
    WPI program state callback [encode n, .number (Float.Model.ofNat index)] (fun result after =>
      result = out (g n) ∧ inv after ∧ after.env = state.env)

/-- Accumulating callbacks for `reduce`. -/
def NativeReducer (program : Program) (inv : State → Prop) (callback : Value) (encode : κ → Value)
    (out : μ → Value) (g : μ → κ → μ) : Prop :=
  ∀ state (acc : μ) (n : κ) (index : Nat), inv state →
    WPI program state callback [out acc, encode n, .number (Float.Model.ofNat index)] (fun result after =>
      result = out (g acc n) ∧ inv after ∧ after.env = state.env)

theorem traverse_map_native {program : Program} {inv : State → Prop} {callback : Value}
    {encode : κ → Value} {out : μ → Value} {g : κ → μ} (spec : NativeCallback program inv callback encode out g) :
    ∀ (ns : List κ) (state : State) (index : Nat), inv state →
      WPTraverse program state callback (ns.map encode) index "map" (fun results after =>
        results = (ns.map g).map out ∧ inv after ∧ after.env = state.env) := by
  intro ns
  induction ns with
  | nil => intro state index held; exact WPTraverse.nil ⟨rfl, held, rfl⟩
  | cons n ns ih =>
    intro state index held
    refine WPTraverse.cons ((spec state n index held).mono ?_)
    rintro y middle ⟨rfl, held', env'⟩
    refine (ih middle (index + 1) held').mono ?_
    rintro ys after ⟨rfl, held'', env''⟩
    exact ⟨by simp, held'', env''.trans env'⟩

theorem traverse_filter_native {program : Program} {inv : State → Prop} {callback : Value}
    {encode : κ → Value} {g : κ → Bool} (spec : NativeCallback program inv callback encode .boolean g) :
    ∀ (ns : List κ) (state : State) (index : Nat), inv state →
      WPTraverse program state callback (ns.map encode) index "filter" (fun results after =>
        results = (ns.filter g).map encode ∧ inv after ∧ after.env = state.env) := by
  intro ns
  induction ns with
  | nil => intro state index held; exact WPTraverse.nil ⟨rfl, held, rfl⟩
  | cons n ns ih =>
    intro state index held
    refine WPTraverse.cons ((spec state n index held).mono ?_)
    rintro y middle ⟨rfl, held', env'⟩
    refine (ih middle (index + 1) held').mono ?_
    rintro ys after ⟨rfl, held'', env''⟩
    refine ⟨?_, held'', env''.trans env'⟩
    cases h : g n <;> simp [h, Value.truthy]

theorem reduce_native {program : Program} {inv : State → Prop} {callback : Value}
    {encode : κ → Value} {out : μ → Value} {g : μ → κ → μ} (spec : NativeReducer program inv callback encode out g) :
    ∀ (ns : List κ) (state : State) (acc : μ) (index : Nat), inv state →
      WPReduce program state callback (ns.map encode) (out acc) index (fun result after =>
        result = out (ns.foldl g acc) ∧ inv after ∧ after.env = state.env) := by
  intro ns
  induction ns with
  | nil => intro state acc index held; exact WPReduce.nil ⟨rfl, held, rfl⟩
  | cons n ns ih =>
    intro state acc index held
    refine WPReduce.cons ((spec state acc n index held).mono ?_)
    rintro y middle ⟨rfl, held', env'⟩
    refine (ih middle _ (index + 1) held').mono ?_
    rintro result after ⟨rfl, held'', env''⟩
    exact ⟨rfl, held'', env''.trans env'⟩

theorem search_native {program : Program} {inv : State → Prop} {callback : Value}
    {encode : κ → Value} {g : κ → Bool} (spec : NativeCallback program inv callback encode .boolean g) (mode : String)
    (supported : mode = "some" ∨ mode = "every" ∨ mode = "find") :
    ∀ (ns : List κ) (state : State) (index : Nat), inv state →
      WPSearch program state callback (ns.map encode) index mode (fun result after =>
        result = (if mode == "find" then ((ns.find? g).map encode).getD .undefined
          else if mode == "every" then .boolean (ns.all g) else .boolean (ns.any g)) ∧
        inv after ∧ after.env = state.env) := by
  have notIndex : (mode == "findIndex") = false := by rcases supported with rfl | rfl | rfl <;> rfl
  intro ns
  induction ns with
  | nil =>
    intro state index held
    refine WPSearch.nil ⟨?_, held, rfl⟩
    rcases supported with rfl | rfl | rfl <;> rfl
  | cons n ns ih =>
    intro state index held
    refine WPSearch.cons ((spec state n index held).mono ?_)
    rintro y middle ⟨rfl, held', env'⟩
    rcases supported with rfl | rfl | rfl
    all_goals
      cases h : g n
      all_goals simp only [h, Value.truthy, notIndex]
      all_goals first
        | exact ⟨by simp [h], held', env'⟩
        | (refine (ih middle (index + 1) held').mono ?_
           rintro result after ⟨rfl, held'', env''⟩
           exact ⟨by simp [h], held'', env''.trans env'⟩)

/-! ## Arrays of scalars -/

namespace Shallow.Adequacy
open Shallow DataRelation

theorem elements_codec_iff (codec : ScalarCodec κ) {heap : Heap} {values : List Value} {natives : List κ}
    {footprint : Heap.Footprint} :
    Elements codec.relation heap values natives footprint ↔
      values = natives.map codec.encode ∧ (∀ x ∈ natives, codec.valid x) ∧ footprint = [] := by
  constructor
  · intro h
    induction h with
    | nil => simp
    | cons head _ _ ih =>
      obtain ⟨⟨valid, rfl⟩, rfl⟩ := codec.holds.mp head
      obtain ⟨rfl, valids, rfl⟩ := ih
      refine ⟨rfl, ?_, rfl⟩
      intro x member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid
      · exact valids x member
  · rintro ⟨rfl, valid, rfl⟩
    induction natives with
    | nil => exact .nil
    | cons x xs ih =>
      exact .cons (codec.holds.mpr ⟨⟨valid x (by simp), rfl⟩, rfl⟩)
        (ih (fun y member => valid y (by simp [member]))) (by simp [Heap.Disjoint])

/-- An array of scalars is one heap object holding the encoded elements. -/
theorem array_codec_iff (codec : ScalarCodec κ) {heap : Heap} {value : Value} {natives : List κ}
    {footprint : Heap.Footprint} :
    (array codec.relation).Holds heap value natives footprint ↔
      natives.length < 4294967296 ∧ (∀ x ∈ natives, codec.valid x) ∧
        ∃ a, value = .ref a ∧ heap[a]? = some (.array (natives.map codec.encode)) ∧ footprint = [a] := by
  constructor
  · rintro ⟨short, a, object, children, rfl, lookup, ⟨values, project, related⟩, _, rfl⟩
    have hobj : object = .array values := by cases object <;> simp_all
    subst hobj
    obtain ⟨rfl, valid, rfl⟩ := (elements_codec_iff codec).mp related
    exact ⟨short, valid, a, rfl, lookup, rfl⟩
  · rintro ⟨short, valid, a, rfl, lookup, rfl⟩
    exact ⟨short, a, _, [], rfl, lookup, ⟨_, rfl, (elements_codec_iff codec).mpr ⟨rfl, valid, rfl⟩⟩,
      by simp, rfl⟩

theorem option_codec_holds (codec : ScalarCodec κ) {heap : Heap} (o : Option κ)
    (valid : ∀ x, o = some x → codec.valid x) :
    (option codec.relation).Holds heap ((o.map codec.encode).getD .undefined) o [] := by
  cases o with
  | none => exact ⟨rfl, rfl⟩
  | some x => exact codec.holds.mpr ⟨⟨valid x rfl, rfl⟩, rfl⟩

def ScalarCodec.bigint : ScalarCodec Int where
  encode := .bigint
  valid := fun _ => True
  relation := DataRelation.int
  holds := by intros; simp [DataRelation.int, DataRelation.scalar]

def ScalarCodec.number : ScalarCodec Float.Model where
  encode := .number
  valid := fun _ => True
  relation := DataRelation.number
  holds := by intros; simp [DataRelation.number, DataRelation.scalar]

def ScalarCodec.boolean : ScalarCodec Bool where
  encode := .boolean
  valid := fun _ => True
  relation := DataRelation.bool
  holds := by intros; simp [DataRelation.bool, DataRelation.scalar]

end Shallow.Adequacy

end Ariadne
