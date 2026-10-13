import Examples.Proofs.ReferenceTree
import Ariadne.Shallow.Adequacy.WPTactic
import Ariadne.Shallow.Adequacy.ScalarMap
import Ariadne.SourceTrace

/-!
# The tree, transferred to its TypeScript source

Every method of `examples/reference/tree.ts`, run by the original evaluator on
any heap that represents a native state, returns what the emitted Lean method
returns and leaves a heap that represents the emitted method's new state.

A child list is an array held by reference in the `children` map. Methods never
mutate an array in place: `filter`, spreads and literals allocate a fresh array
and the map entry is pointed at it.
-/

namespace Examples.ReferenceSource.Tree
open Ariadne Ariadne.Shallow Ariadne.Shallow.Adequacy Extracted_reference_tree.Shallow
open Heap

abbrev P := Extracted_reference_tree.program
abbrev State' := NativeTypes.«Tree#state»

def stringStrings : List (JSString × JSString) → List (Value × Value) :=
  encodeEntries .string .string

/-- The `children` map's entries: each key's child list is an array, outside the two maps. -/
def Children (heap : Heap) (pA cA : Nat) : List (Value × Value) → List (JSString × List JSString) → Prop
  | [], [] => True
  | kv :: enc, e :: es => kv.1 = .string e.1 ∧
      (∃ a, kv.2 = .ref a ∧ heap[a]? = some (.array (e.2.map .string)) ∧ a ≠ pA ∧ a ≠ cA) ∧
      Children heap pA cA enc es
  | [], _ :: _ => False
  | _ :: _, [] => False

/-- The heap shape of a tree: an instance whose two private fields reference the
parent map, holding the encoded entries, and the children map. -/
structure Layout (heap : Heap) (address : Nat) (native : State') (pA cA : Nat) : Prop where
  instance_ : heap[address]? = some (.instance_ "Tree" [("parents", .ref pA), ("children", .ref cA)])
  parentsMap : heap[pA]? = some (.map (stringStrings native.parents.entries))
  childrenMap : ∃ enc, heap[cA]? = some (.map enc) ∧ Children heap pA cA enc native.children.entries
  distinct : pA ≠ cA ∧ address ≠ pA ∧ address ≠ cA

/-- A call keeps every object it found, except the two maps. -/
def Keeps (before after : Heap) (pA cA : Nat) : Prop :=
  before.length ≤ after.length ∧ ∀ i, i < before.length → i ≠ pA → i ≠ cA → after[i]? = before[i]?

theorem Keeps.refl (heap : Heap) (pA cA : Nat) : Keeps heap heap pA cA := ⟨Nat.le_refl _, fun _ _ _ _ => rfl⟩

theorem Keeps.trans {a b c : Heap} {pA cA : Nat} (ab : Keeps a b pA cA) (bc : Keeps b c pA cA) :
    Keeps a c pA cA :=
  ⟨Nat.le_trans ab.1 bc.1, fun i hi np nc => (bc.2 i (by have := ab.1; omega) np nc).trans (ab.2 i hi np nc)⟩

/-! ## Children entries -/

theorem Children.length {heap : Heap} {pA cA : Nat} :
    ∀ {enc : List (Value × Value)} {es : List (JSString × List JSString)},
      Children heap pA cA enc es → enc.length = es.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [Children.length h.2.2]

theorem Children.mono {heap heap' : Heap} {pA cA : Nat}
    (agree : ∀ i, i < heap.length → i ≠ pA → i ≠ cA → heap'[i]? = heap[i]?) :
    ∀ {enc : List (Value × Value)} {es : List (JSString × List JSString)},
      Children heap pA cA enc es → Children heap' pA cA enc es
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨key, ⟨a, value, lookup, np, nc⟩, rest⟩ =>
    ⟨key, ⟨a, value, (agree a (bound_of_some lookup) np nc).trans lookup, np, nc⟩, Children.mono agree rest⟩

theorem mapGet_cons_ne {k key v : Value} {xs : List (Value × Value)} (h : sameValueZero k key = false) :
    mapGet ((k, v) :: xs) key = mapGet xs key := by
  simp [mapGet, h]

theorem mapHas_cons_ne {k key v : Value} {xs : List (Value × Value)} (h : sameValueZero k key = false) :
    mapHas ((k, v) :: xs) key = mapHas xs key := by
  simp [mapHas, h]

theorem Children.get_none {heap : Heap} {pA cA : Nat} {k : JSString} :
    ∀ {enc : List (Value × Value)} {es : List (JSString × List JSString)},
      Children heap pA cA enc es → MapEntries.get es k = none → mapGet enc (.string k) = .undefined
  | [], [], _, _ => rfl
  | (kk, kv) :: enc, (ek, ev) :: es, ⟨key, _, rest⟩, missing => by
    simp only at key
    subst key
    by_cases same : (ek == k) = true
    · simp [MapEntries.get, same] at missing
    · simp only [MapEntries.get, same, Bool.false_eq_true, ↓reduceIte] at missing
      rw [mapGet_cons_ne (by rw [sameValueZero_string]; simpa using same)]
      exact Children.get_none rest missing

theorem Children.get_some {heap : Heap} {pA cA : Nat} {k : JSString} {v : List JSString} :
    ∀ {enc : List (Value × Value)} {es : List (JSString × List JSString)},
      Children heap pA cA enc es → MapEntries.get es k = some v →
      ∃ a, mapGet enc (.string k) = .ref a ∧ heap[a]? = some (.array (v.map .string)) ∧ a ≠ pA ∧ a ≠ cA
  | [], [], _, found => by simp [MapEntries.get] at found
  | (kk, kv) :: enc, (ek, ev) :: es, ⟨key, ⟨a, value, lookup, np, nc⟩, rest⟩, found => by
    simp only at key value
    subst key value
    by_cases same : (ek == k) = true
    · simp only [MapEntries.get, same, ↓reduceIte, Option.some.injEq] at found
      subst found
      exact ⟨a, by simp [mapGet, sameValueZero_string, same], lookup, np, nc⟩
    · simp only [MapEntries.get, same, Bool.false_eq_true, ↓reduceIte] at found
      rw [mapGet_cons_ne (by rw [sameValueZero_string]; simpa using same)]
      exact Children.get_some rest found

theorem Children.has {heap : Heap} {pA cA : Nat} {k : JSString} :
    ∀ {enc : List (Value × Value)} {es : List (JSString × List JSString)},
      Children heap pA cA enc es → mapHas enc (.string k) = (MapEntries.get es k).isSome
  | [], [], _ => rfl
  | (kk, kv) :: enc, (ek, ev) :: es, ⟨key, _, rest⟩ => by
    simp only at key
    subst key
    by_cases same : (ek == k) = true
    · simp [mapHas, MapEntries.get, sameValueZero_string, same]
    · rw [mapHas_cons_ne (by rw [sameValueZero_string]; simpa using same)]
      simp only [MapEntries.get, same, Bool.false_eq_true, ↓reduceIte]
      exact Children.has rest

theorem Children.set {heap : Heap} {pA cA : Nat} {k : JSString} {v : List JSString} {a : Nat}
    (lookup : heap[a]? = some (.array (v.map .string))) (np : a ≠ pA) (nc : a ≠ cA) :
    ∀ {enc : List (Value × Value)} {es : List (JSString × List JSString)},
      Children heap pA cA enc es →
      Children heap pA cA (mapSet enc (.string k) (.ref a)) (MapEntries.set es k v)
  | [], [], _ => ⟨rfl, ⟨a, rfl, lookup, np, nc⟩, trivial⟩
  | (kk, kv) :: enc, (ek, ev) :: es, ⟨key, old, rest⟩ => by
    simp only at key
    subst key
    by_cases same : (ek == k) = true
    · simp only [mapSet, sameValueZero_string, same, ↓reduceIte, MapEntries.set]
      exact ⟨rfl, ⟨a, rfl, lookup, np, nc⟩, rest⟩
    · have ne : sameValueZero (.string ek) (.string k) = false := by rw [sameValueZero_string]; simpa using same
      simp only [mapSet, ne, Bool.false_eq_true, ↓reduceIte, MapEntries.set, same]
      exact ⟨rfl, old, Children.set lookup np nc rest⟩

/-! ## Layouts -/

theorem Layout.rewrite {heap heap' : Heap} {address : Nat} {native : State'} {pA cA : Nat}
    (l : Layout heap address native pA cA) (native' : State')
    (agree : ∀ i, i < heap.length → i ≠ pA → i ≠ cA → heap'[i]? = heap[i]?)
    (parents : heap'[pA]? = some (.map (stringStrings native'.parents.entries)))
    (children : ∃ enc, heap'[cA]? = some (.map enc) ∧ Children heap' pA cA enc native'.children.entries) :
    Layout heap' address native' pA cA := by
  obtain ⟨d1, d2, d3⟩ := l.distinct
  exact ⟨(agree address (bound_of_some l.instance_) d2 d3).trans l.instance_, parents, children, l.distinct⟩

/-- A call that keeps the two maps' objects keeps the layout. -/
theorem Layout.extend {heap heap' : Heap} {address : Nat} {native : State'} {pA cA : Nat}
    (l : Layout heap address native pA cA) (agree : ∀ i, i < heap.length → heap'[i]? = heap[i]?) :
    Layout heap' address native pA cA := by
  obtain ⟨enc, lookup, rest⟩ := l.childrenMap
  exact l.rewrite native (fun i hi _ _ => agree i hi) ((agree _ (bound_of_some l.parentsMap)).trans l.parentsMap)
    ⟨enc, (agree _ (bound_of_some lookup)).trans lookup, rest.mono (fun i hi _ _ => agree i hi)⟩

theorem Keeps.of_agree {heap heap' : Heap} {pA cA : Nat} (longer : heap.length ≤ heap'.length)
    (agree : ∀ i, i < heap.length → heap'[i]? = heap[i]?) : Keeps heap heap' pA cA :=
  ⟨longer, fun i hi _ _ => agree i hi⟩

/-! ## Method lookup -/

def treeClass : Ariadne.Class := P.classes[0]!
theorem treeFind : P.classes.find? (·.name == treeClass.name) = some treeClass := by kernel_rfl
theorem treeName : treeClass.name = "Tree" := by kernel_rfl

def method (index : Nat) : Ariadne.Function := treeClass.methods[index]!
theorem methodFind (index : Nat) (bound : index < 5 := by decide) :
    treeClass.methods.find? (·.name == (method index).name) = some (method index) := by
  rcases index with _ | _ | _ | _ | _ | index
  all_goals first | kernel_rfl | omega

/-- Unfold a method of the class into its literal body and parameters. -/
scoped macro "unfold_method" : tactic => `(tactic| (
  conv => arg 3; simp only [method, treeClass, P, Extracted_reference_tree.program,
    List.getElem!_cons_zero, List.getElem!_cons_succ]
  conv => arg 2; simp only [method, treeClass, P, Extracted_reference_tree.program,
    List.getElem!_cons_zero, List.getElem!_cons_succ]))

theorem mapGet_stringStrings (xs : List (JSString × JSString)) (k : JSString) :
    mapGet (stringStrings xs) (.string k) = ((MapEntries.get xs k).map .string).getD .undefined :=
  mapGet_string .string xs k

theorem mapSet_stringStrings (xs : List (JSString × JSString)) (k v : JSString) :
    mapSet (stringStrings xs) (.string k) (.string v) = stringStrings (MapEntries.set xs k v) :=
  mapSet_string .string xs k v

theorem mapDelete_stringStrings (xs : List (JSString × JSString)) (k : JSString) :
    mapDelete (stringStrings xs) (.string k) = stringStrings (MapEntries.delete xs k) :=
  mapDelete_string .string xs k

set_option hygiene false in
/-- Name every fact of the input layout for the evaluation steps. -/
scoped macro "layout_facts" : tactic => `(tactic| (
  obtain ⟨ha, inst⟩ := getElem_of_some input.instance_
  obtain ⟨hp, pMap⟩ := getElem_of_some input.parentsMap
  obtain ⟨enc, cLookup, children⟩ := input.childrenMap
  obtain ⟨hc, cMap⟩ := getElem_of_some cLookup
  obtain ⟨d1, d2, d3⟩ := input.distinct
  have e1 := Ne.symm d1; have e2 := Ne.symm d2; have e3 := Ne.symm d3))

/-! ## `parent`, `add` and `childList` -/

theorem parent_source (before : State) (address : Nat) (native : State') (pA cA : Nat) (node : JSString)
    (input : Layout before.heap address native pA cA) :
    WPI P before (.method address "parent") [.string node] (fun result after =>
      result = ((«Tree#parent» native node).map .string).getD .undefined ∧
      Layout after.heap address native pA cA ∧ Keeps before.heap after.heap pA cA ∧ after.env = before.env) := by
  layout_facts
  change WPI P before (.method address (method 1).name) _ _
  refine WPI.method (class_ := treeClass) (by rw [treeName]; exact input.instance_) treeFind (methodFind 1) ?_
  unfold_method
  wp
  refine ⟨by simp, ?_, ?_, ?_, by first | rfl | trivial⟩
  · simp [stringStrings, mapGet_string, «Tree#parent», JSMap.get, NativeDestruct.«Tree#state»]
  · exact input.extend (fun i hi => by simp [bindArguments, State.declare, State.alloc, List.getElem?_append_left hi])
  · exact Keeps.of_agree (by simp [bindArguments, State.declare, State.alloc])
      (fun i hi => by simp [bindArguments, State.declare, State.alloc, List.getElem?_append_left hi])

theorem add_source (before : State) (address : Nat) (native : State') (pA cA : Nat) (node : JSString)
    (input : Layout before.heap address native pA cA) :
    WPI P before (.method address "add") [.string node] (fun result after =>
      result = .undefined ∧ Layout after.heap address (Examples.Proofs.ReferenceTree.add native node) pA cA ∧
      Keeps before.heap after.heap pA cA ∧ after.env = before.env) := by
  layout_facts
  change WPI P before (.method address (method 0).name) _ _
  refine WPI.method (class_ := treeClass) (by rw [treeName]; exact input.instance_) treeFind (methodFind 0) ?_
  unfold_method
  cases seen : MapEntries.get native.children.entries node with
  | some v =>
    have has : mapHas enc (.string node) = true := by rw [children.has, seen]; rfl
    wp
    have kept : Examples.Proofs.ReferenceTree.add native node = native := by
      simp [Examples.Proofs.ReferenceTree.add, JSMap.has, JSMap.get, seen]
    rw [kept]
    refine ⟨by simp, trivial, ?_, ?_, trivial⟩
    · exact input.extend (fun i hi => by simp [bindArguments, State.declare, State.alloc, List.getElem?_append_left hi])
    · exact Keeps.of_agree (by simp [bindArguments, State.declare, State.alloc])
        (fun i hi => by simp [bindArguments, State.declare, State.alloc, List.getElem?_append_left hi])
  | none =>
    have has : mapHas enc (.string node) = false := by rw [children.has, seen]; rfl
    wp
    have added : Examples.Proofs.ReferenceTree.add native node =
        { native with children := native.children.set node [] } := by
      simp [Examples.Proofs.ReferenceTree.add, JSMap.has, JSMap.get, seen]
    rw [added]
    simp only [bindArguments, State.declare, State.alloc, List.zip_cons_cons, List.zip_nil_right,
      List.foldl_cons, List.foldl_nil, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    refine ⟨by simp, trivial, ?_, ?_, trivial⟩
    · refine input.rewrite _ (fun i hi np nc => ?_) ?_
        ⟨_, ?_, Children.set (a := before.heap.length + 1 + 1) ?_ ?_ ?_ (children.mono (fun i hi np nc => ?_))⟩
      all_goals heap_simp
      all_goals first | rfl | omega | exact input.parentsMap | done
    · refine ⟨by simp, fun i hi np nc => ?_⟩
      heap_simp

theorem childList_source (before : State) (address : Nat) (native : State') (pA cA : Nat) (node : JSString)
    (input : Layout before.heap address native pA cA) :
    WPI P before (.method address "childList") [.string node] (fun result after =>
      (∃ r, result = .ref r ∧ before.heap.length ≤ r ∧
        after.heap[r]? = some (.array ((«Tree#childList» native node).map .string))) ∧
      Layout after.heap address native pA cA ∧ Keeps before.heap after.heap pA cA ∧ after.env = before.env) := by
  layout_facts
  change WPI P before (.method address (method 2).name) _ _
  refine WPI.method (class_ := treeClass) (by rw [treeName]; exact input.instance_) treeFind (methodFind 2) ?_
  unfold_method
  cases seen : MapEntries.get native.children.entries node with
  | some v =>
    obtain ⟨a, mg, lookup, na, nc⟩ := children.get_some seen
    obtain ⟨hla, arr⟩ := getElem_of_some lookup
    wp
    have list : «Tree#childList» native node = v := by
      simp [«Tree#childList», JSMap.get, NativeDestruct.«Tree#state», seen]
    rw [list]
    simp only [bindArguments, State.declare, State.alloc, List.zip_cons_cons, List.zip_nil_right,
      List.foldl_cons, List.foldl_nil, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    refine ⟨by simp, ⟨_, rfl, by omega, ?_⟩, ?_, ?_, trivial⟩
    · heap_simp
    · exact input.extend (fun i hi => by heap_simp)
    · exact Keeps.of_agree (by simp) (fun i hi => by heap_simp)
  | none =>
    have mg := children.get_none seen
    wp
    have list : «Tree#childList» native node = [] := by
      simp [«Tree#childList», JSMap.get, NativeDestruct.«Tree#state», seen]
    rw [list]
    simp only [bindArguments, State.declare, State.alloc, List.zip_cons_cons, List.zip_nil_right,
      List.foldl_cons, List.foldl_nil, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    refine ⟨by simp, ⟨_, rfl, by omega, ?_⟩, ?_, ?_, trivial⟩
    · heap_simp
      try simp
    · exact input.extend (fun i hi => by heap_simp)
    · exact Keeps.of_agree (by simp) (fun i hi => by heap_simp)

/-! ## `root`: a counted walk up the parent links -/

def rootParts : Expr × Stmt × Stmt :=
  match (method 4).body with
  | .block [_, .for_ _ guard update body _, _] _ => (guard, update, body)
  | _ => default

/-- The loop state of `root`: the call's four bindings, and the heap the call began with. -/
structure RootFrame (st : State) (heap0 : Heap) (address : Nat) (cursor : JSString) (k : Nat) : Prop where
  env : st.env = [("i", heap0.length + 3), ("cursor", heap0.length + 2), ("node", heap0.length + 1),
    ("this", heap0.length)]
  keep : ∀ i, i < heap0.length → st.heap[i]? = heap0[i]?
  long : heap0.length + 4 ≤ st.heap.length
  thisCell : st.heap[heap0.length]? = some (.cell (.ref address))
  cursorCell : st.heap[heap0.length + 2]? = some (.cell (.string cursor))
  iCell : st.heap[heap0.length + 3]? = some (.cell (.number (Float.Model.ofInt k)))

theorem root_loop (heap0 : Heap) (address : Nat) (native : State') (pA cA : Nat)
    (input : Layout heap0 address native pA cA) (enc : List (Value × Value))
    (cLookup : heap0[cA]? = some (.map enc)) (len : enc.length = native.children.size)
    (range : Int53.InRange (native.children.size : Int)) :
    ∀ m k cursor st, k + m = native.children.size → RootFrame st heap0 address cursor k →
      WPLoop P st rootParts.1 rootParts.2.2 (some rootParts.2.1) (fun out =>
        (∀ i, i < heap0.length → out.state.heap[i]? = heap0[i]?) ∧
        ((out.control = .returned ∧ out.value = .string (Examples.Proofs.ReferenceTree.walk native m cursor)) ∨
         (out.control = .normal ∧ out.state.env = st.env ∧ heap0.length + 4 ≤ out.state.heap.length ∧
          out.state.heap[heap0.length + 2]? =
            some (.cell (.string (Examples.Proofs.ReferenceTree.walk native m cursor)))))) := by
  intro m
  induction m with
  | zero =>
    intro k cursor st count frame
    have henv := frame.env
    obtain ⟨hl3, iCell⟩ := getElem_of_some frame.iCell
    obtain ⟨hl0, thisCell⟩ := getElem_of_some frame.thisCell
    have inst := (frame.keep address (bound_of_some input.instance_)).trans input.instance_
    obtain ⟨ha, inst⟩ := getElem_of_some inst
    have cMap := (frame.keep cA (bound_of_some cLookup)).trans cLookup
    obtain ⟨hc, cMap⟩ := getElem_of_some cMap
    have stop : ¬ (Float.Model.ofInt (k : Int) < Float.Model.ofNat native.children.size) := by
      rw [ofNat_ofInt, Int53.lt_ofInt _ _ (Int53.nat_range (by omega) range) range]
      omega
    conv => arg 3; simp only [rootParts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    conv => arg 4; simp only [rootParts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    conv => arg 5; simp only [rootParts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    refine WPLoop.step ?_
    wp
    exact ⟨frame.keep, Or.inr ⟨trivial, trivial, frame.long, frame.cursorCell⟩⟩
  | succ m ih =>
    intro k cursor st count frame
    have henv := frame.env
    obtain ⟨hl3, iCell⟩ := getElem_of_some frame.iCell
    obtain ⟨hl2, cursorCell⟩ := getElem_of_some frame.cursorCell
    obtain ⟨hl0, thisCell⟩ := getElem_of_some frame.thisCell
    have inst := (frame.keep address (bound_of_some input.instance_)).trans input.instance_
    obtain ⟨ha, inst⟩ := getElem_of_some inst
    have cMap := (frame.keep cA (bound_of_some cLookup)).trans cLookup
    obtain ⟨hc, cMap⟩ := getElem_of_some cMap
    have pMap := (frame.keep pA (bound_of_some input.parentsMap)).trans input.parentsMap
    obtain ⟨hp, pMap⟩ := getElem_of_some pMap
    have go : Float.Model.ofInt (k : Int) < Float.Model.ofNat native.children.size := by
      rw [ofNat_ofInt, Int53.lt_ofInt _ _ (Int53.nat_range (by omega) range) range]
      omega
    conv => arg 3; simp only [rootParts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    conv => arg 4; simp only [rootParts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    conv => arg 5; simp only [rootParts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    refine WPLoop.step ?_
    cases up : MapEntries.get native.parents.entries cursor with
    | none =>
      have pget : mapGet (stringStrings native.parents.entries) (.string cursor) = .undefined := by
        rw [mapGet_stringStrings, up]; rfl
      wp
      have w : Examples.Proofs.ReferenceTree.walk native (m + 1) cursor = cursor := by
        simp [Examples.Proofs.ReferenceTree.walk, JSMap.get, up]
      refine ⟨fun i hi => ?_, Or.inl ⟨trivial, by rw [w]⟩⟩
      have := frame.long
      simp only [State.declare, State.alloc]
      heap_simp
      exact frame.keep i hi
    | some p =>
      have pget : mapGet (stringStrings native.parents.entries) (.string cursor) = .string p := by
        rw [mapGet_stringStrings, up]; rfl
      wp
      refine ⟨_, assign_eq (loc := heap0.length + 2) (other := "cursor") (by wp_eval)
        (by simp [State.declare, State.alloc]; omega), ?_⟩
      wp
      have step : Float.Model.ofInt (k : Int) + Float.Model.ofScientific 1 0 = Float.Model.ofInt ((k + 1 : Nat) : Int) := by
        rw [one_scientific, ← Int53.add_exact _ _ (Int53.nat_range (by omega) range) (by decide)
          (by exact_mod_cast Int53.nat_range (by omega) range)]
        rfl
      rw [step]
      refine ⟨_, assign_eq (loc := heap0.length + 3) (other := "i") (by wp_eval)
        (by simp [State.declare, State.alloc]; omega), ?_⟩
      have w : Examples.Proofs.ReferenceTree.walk native (m + 1) cursor =
          Examples.Proofs.ReferenceTree.walk native m p := by
        simp [Examples.Proofs.ReferenceTree.walk, JSMap.get, up]
      rw [w]
      have long := frame.long
      refine ih (k + 1) p _ (by omega) ⟨rfl, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp only [State.declare, State.alloc]
      all_goals heap_simp
      · exact frame.keep i hi
      · omega
      · exact frame.thisCell

theorem root_source (before : State) (address : Nat) (native : State') (pA cA : Nat) (node : JSString)
    (range : Int53.InRange (native.children.size : Int)) (input : Layout before.heap address native pA cA) :
    WPI P before (.method address "root") [.string node] (fun result after =>
      result = .string («Tree#root» native node) ∧
      Layout after.heap address native pA cA ∧ Keeps before.heap after.heap pA cA ∧ after.env = before.env) := by
  layout_facts
  have loop := root_loop before.heap address native pA cA input enc cLookup children.length range
    native.children.size 0 node
  simp only [rootParts, method, treeClass, P, Extracted_reference_tree.program,
    List.getElem!_cons_zero, List.getElem!_cons_succ] at loop
  change WPI P before (.method address (method 4).name) _ _
  refine WPI.method (class_ := treeClass) (by rw [treeName]; exact input.instance_) treeFind (methodFind 4) ?_
  unfold_method
  wp
  refine WPS.for_ ?_
  wp
  rw [zero_scientific]
  refine (loop _ (by simp) ⟨?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩).mono ?_
  all_goals try simp only [bindArguments, State.declare, State.alloc, List.zip_cons_cons, List.zip_nil_right,
      List.foldl_cons, List.foldl_nil]
  all_goals try heap_simp
  · omega
  · rfl
  · intro out ⟨keep, finished⟩
    rw [Examples.Proofs.ReferenceTree.root_eq]
    rcases finished with ⟨ret, value⟩ | ⟨normal, env, long, cell⟩
    · simp only [ret, reduceCtorEq, ↓reduceIte]
      exact ⟨Or.inr trivial, value, input.extend keep, Keeps.of_agree (length_le_of_agree keep) keep, trivial⟩
    · simp only [normal, ↓reduceIte]
      obtain ⟨hl2, cell'⟩ := getElem_of_some cell
      wp
      exact ⟨by simp, by simp, input.extend keep, Keeps.of_agree (length_le_of_agree keep) keep, trivial⟩

end Examples.ReferenceSource.Tree
