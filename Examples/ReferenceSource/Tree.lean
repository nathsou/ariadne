import Examples.ReferenceSource.TreeMove
import Ariadne.Shallow.Adequacy.ClassConstruction

/-!
# The tree, transferred to its TypeScript source: traces

A fresh `new Tree()` followed by any sequence of `add` and `move` calls, run by
the original evaluator, keeps the instance representing the emitted state after
the same calls. The two reference theorems then hold of the source program:
`root` always reaches a node without a parent, and a node is in its parent's
child list exactly when `parent` names that parent.

The only side conditions are the evaluator's resource limits: before each
`move`, the node count stays a safe integer (the loop counter is a float) and
every child list stays below the dense-array length limit.
-/

namespace Examples.ReferenceSource.Tree
open Ariadne Ariadne.Shallow Ariadne.Shallow.Adequacy Extracted_reference_tree.Shallow
open Examples.Proofs.ReferenceTree (detached hits Reachable)

/-! ## Resource bounds -/

/-- The evaluator's limits, for the state a `move` starts from. -/
def Fits (s : State') : Prop :=
  s.children.size + 3 ≤ 9007199254740991 ∧ ∀ k v, s.children.get k = some v → v.length + 1 < 4294967296

theorem size_set_le {α : Type} (m : JSMap JSString α) (k : JSString) (v : α) : (m.set k v).size ≤ m.size + 1 := by
  rw [JSMap.size_set]; split <;> omega

theorem add_size (s : State') (n : JSString) :
    (Examples.Proofs.ReferenceTree.add s n).children.size ≤ s.children.size + 1 := by
  unfold Examples.Proofs.ReferenceTree.add
  split
  · omega
  · exact size_set_le _ _ _

theorem add_lists {s : State'} {n k : JSString} {v : List JSString}
    (h : (Examples.Proofs.ReferenceTree.add s n).children.get k = some v) : s.children.get k = some v ∨ v = [] := by
  unfold Examples.Proofs.ReferenceTree.add at h
  split at h
  · exact Or.inl h
  · by_cases same : n = k
    · subst same; simp at h; exact Or.inr (by simp_all)
    · simp [same] at h; exact Or.inl h

theorem detached_size (a : State') (n : JSString) : (detached a n).children.size ≤ a.children.size + 1 := by
  cases h : a.parents.get n
  · simp [detached, h]
  · simp only [detached, h]; exact size_set_le _ _ _

theorem detached_lists {a : State'} {n k : JSString} {v : List JSString}
    (h : (detached a n).children.get k = some v) :
    (∃ w, a.children.get k = some w ∧ v.length ≤ w.length) ∨ v = [] := by
  cases hp : a.parents.get n with
  | none => simp [detached, hp] at h; exact Or.inl ⟨v, h, Nat.le_refl _⟩
  | some old =>
    by_cases same : old = k
    · subst same
      simp [detached, hp] at h
      subst h
      cases hw : a.children.get old with
      | none => simp
      | some w => exact Or.inl ⟨w, rfl, List.length_filter_le _ _⟩
    · simp [detached, hp, same] at h
      exact Or.inl ⟨v, h, Nat.le_refl _⟩

theorem detached_bounds (s a : State') (node : JSString) (parent : Option JSString)
    (small : s.children.size + 3 ≤ 9007199254740991) (aSize : a.children.size ≤ s.children.size + 2)
    (aLists : ∀ k v, a.children.get k = some v → v.length + 1 < 4294967296) :
    Int53.InRange ((detached a node).children.size : Int) ∧
      ∀ p, parent = some p → (((detached a node).children.get p).getD []).length + 1 < 4294967296 := by
  refine ⟨?_, fun p _ => ?_⟩
  · have := detached_size a node
    rw [Int53.range_iff_natAbs]
    simp only [Int.natAbs_natCast]
    omega
  · cases h : (detached a node).children.get p with
    | none => simp
    | some v =>
      rcases detached_lists h with ⟨w, hw, le⟩ | rfl
      · have := aLists p w hw; simp; omega
      · simp

/-- The bounds `move` needs, from the state it starts in. -/
theorem move_bounds (s : State') (fits : Fits s) (node : JSString) (parent : Option JSString) :
    Int53.InRange ((detached (parent.elim (Examples.Proofs.ReferenceTree.add s node)
      (Examples.Proofs.ReferenceTree.add (Examples.Proofs.ReferenceTree.add s node))) node).children.size : Int) ∧
      ∀ p, parent = some p → (((detached (parent.elim (Examples.Proofs.ReferenceTree.add s node)
        (Examples.Proofs.ReferenceTree.add (Examples.Proofs.ReferenceTree.add s node))) node).children.get p).getD
          []).length + 1 < 4294967296 := by
  obtain ⟨small, lists⟩ := fits
  refine detached_bounds s _ node parent small ?_ ?_
  · cases parent with
    | none => have := add_size s node; simp only [Option.elim]; omega
    | some p =>
      have := add_size s node
      have := add_size (Examples.Proofs.ReferenceTree.add s node) p
      simp only [Option.elim]; omega
  · intro k v h
    cases parent with
    | none =>
      rcases add_lists h with h | rfl
      · exact lists k v h
      · simp
    | some p =>
      rcases add_lists h with h | rfl
      · rcases add_lists h with h | rfl
        · exact lists k v h
        · simp
      · simp

/-- `move` on a state within the evaluator's limits. -/
theorem move_fits (before : State) (address : Nat) (native : State') (pA cA : Nat) (node : JSString)
    (parent : Option JSString) (fits : Fits native) (input : Layout before.heap address native pA cA) :
    WPI P before (.method address "move") [.string node, optValue parent] (fun result after =>
      result = .undefined ∧ Layout after.heap address (Examples.Proofs.ReferenceTree.move native node parent) pA cA ∧
      Keeps before.heap after.heap pA cA ∧ after.env = before.env) :=
  have bounds := move_bounds native fits node parent
  move_source before address native pA cA node parent input bounds.1 bounds.2

/-! ## Construction -/

theorem treePlain : treeClass.constructor_ = none := by kernel_rfl

/-- `new Tree()` allocates the two empty maps and then the instance. -/
theorem new_source (before : State) (span : Span) :
    let n := before.heap.length
    ∃ after, SourceEvaluates Extracted_reference_tree.source before (.newClass "Tree" [] span) (.ref (n + 2)) after ∧
      Layout after.heap (n + 2) «Tree##new» n (n + 1) := by
  intro n
  have initializers : EvaluatesFields P before (treeClass.fields.map fun f => (f.name, f.value)) []
      [("parents", .ref n), ("children", .ref (n + 1))]
      ((before.alloc (.map [])).2.alloc (.map [])).2 := by
    simp only [treeClass, P, Extracted_reference_tree.program, List.getElem!_cons_zero, List.map_cons,
      List.map_nil]
    refine EvaluatesFields.cons (Evaluates.newMap _ _ _ _ _) ?_ (by decide)
    refine EvaluatesFields.cons (Evaluates.newMap _ _ _ _ _) ?_ (by decide)
    simp only [State.alloc, List.length_append, List.length_cons, List.length_nil, fieldSet, n]
    exact EvaluatesFields.nil _ _ _
  have evaluated := Evaluates.newClass_plain treeFind treePlain (EvaluatesArgs.nil P before) initializers span
  rw [treeName] at evaluated
  have length : ((before.alloc (.map [])).2.alloc (.map [])).2.heap.length = n + 2 := by
    simp [State.alloc, n]
  rw [length] at evaluated
  refine ⟨_, Extracted_reference_tree.certificate.transfer_evaluation evaluated, ?_, ?_, ⟨[], ?_, trivial⟩, ?_,
    fun enc h => ?_, ?_⟩
  all_goals simp [State.alloc, n, «Tree##new», JSMap.empty, stringStrings, encodeEntries,
    NativeConstruct.«Tree#state»] at *
  subst h
  simp

/-! ## Call traces -/

inductive Operation where
  | add (node : JSString)
  | move (node : JSString) (parent : Option JSString)

def applyOp (s : State') : Operation → State'
  | .add node => («Tree#add» s node).2.1
  | .move node parent => («Tree#move» s node parent).2.1

/-- The source call each native operation stands for. -/
def call (address : Nat) : Operation → Value × List Value
  | .add node => (.method address "add", [.string node])
  | .move node parent => (.method address "move", [.string node, optValue parent])

/-- `move` is only claimed within the evaluator's limits; `add` always is. -/
def Pre (s : State') : Operation → Prop
  | .add _ => True
  | .move _ _ => Fits s

/-- Every operation of the sequence starts within its limits. -/
def Runs : State' → List Operation → Prop
  | _, [] => True
  | s, op :: ops => Pre s op ∧ Runs (applyOp s op) ops

theorem operation_source (before : State) (address : Nat) (native : State') (pA cA : Nat) (op : Operation)
    (pre : Pre native op) (input : Layout before.heap address native pA cA) :
    ∃ after, SourceInvokes Extracted_reference_tree.source before (call address op).1 (call address op).2
      .undefined after ∧ Layout after.heap address (applyOp native op) pA cA := by
  cases op with
  | add node =>
    obtain ⟨result, after, invoked, rfl, layout, _⟩ := (add_source before address native pA cA node input).elim
    refine ⟨after, Extracted_reference_tree.certificate.transfer_invocation invoked, ?_⟩
    simp only [applyOp, Examples.Proofs.ReferenceTree.add_eq]
    exact layout
  | move node parent =>
    obtain ⟨result, after, invoked, rfl, layout, _⟩ :=
      (move_fits before address native pA cA node parent pre input).elim
    refine ⟨after, Extracted_reference_tree.certificate.transfer_invocation invoked, ?_⟩
    simp only [applyOp, Examples.Proofs.ReferenceTree.move_eq]
    exact layout

/-- Any sequence of operations within limits, run by the original evaluator,
keeps the instance representing the emitted state after the same operations. -/
theorem trace_source (before : State) (address : Nat) (native : State') (pA cA : Nat) (ops : List Operation)
    (runs : Runs native ops) (input : Layout before.heap address native pA cA) :
    ∃ after, SourceTrace Extracted_reference_tree.source before (ops.map (call address))
      (ops.map fun _ => .undefined) after ∧
      Layout after.heap address (ops.foldl applyOp native) pA cA := by
  induction ops generalizing before native with
  | nil => exact ⟨before, .nil before, input⟩
  | cons op ops ih =>
    obtain ⟨middle, invoked, layout⟩ := operation_source before address native pA cA op runs.1 input
    obtain ⟨after, rest, final⟩ := ih middle _ runs.2 layout
    exact ⟨after, .next invoked rest, final⟩

theorem reachable_fold (ops : List Operation) : ∀ s, Reachable s → Reachable (ops.foldl applyOp s) := by
  induction ops with
  | nil => intro s r; exact r
  | cons op ops ih =>
    intro s r
    cases op with
    | add node => exact ih _ (Reachable.add r node)
    | move node parent => exact ih _ (Reachable.move r node parent)

/-! ## The reference theorems, for the source -/

/-- **Roots have no parent, in the source.** On a fresh tree, after any
sequence of `add` and `move` calls within limits, `root(node)` returns a node
whose `parent` is `undefined`. -/
theorem root_source_reached (before : Ariadne.State) (span : Span) (ops : List Operation)
    (runs : Runs «Tree##new» ops)
    (range : Int53.InRange ((ops.foldl applyOp «Tree##new»).children.size : Int)) (node : JSString) :
    let address := before.heap.length + 2
    ∃ fresh root after,
      SourceEvaluates Extracted_reference_tree.source before (.newClass "Tree" [] span) (.ref address) fresh ∧
      SourceTrace Extracted_reference_tree.source fresh
        (ops.map (call address) ++
          [(.method address "root", [.string node]), (.method address "parent", [.string root])])
        (ops.map (fun _ => .undefined) ++ [.string root, .undefined]) after := by
  intro address
  obtain ⟨fresh, constructed, layout⟩ := new_source before span
  obtain ⟨middle, trace, layout⟩ := trace_source fresh address _ _ _ ops runs layout
  let final := ops.foldl applyOp «Tree##new»
  obtain ⟨_, rooted, rootRun, rfl, rootLayout, _⟩ :=
    (root_source middle address final _ _ node range layout).elim
  obtain ⟨_, after, parentRun, rfl, _⟩ :=
    (parent_source rooted address final _ _ («Tree#root» final node) rootLayout).elim
  have none := Examples.Proofs.ReferenceTree.reachable_root (reachable_fold ops _ .fresh) node
  rw [none] at parentRun
  exact ⟨fresh, «Tree#root» final node, after, constructed, trace.append
    (.next (Extracted_reference_tree.certificate.transfer_invocation rootRun)
      (.next (Extracted_reference_tree.certificate.transfer_invocation parentRun) (.nil _)))⟩

/-- **Child lists agree with parent links, in the source.** On a fresh tree,
after any sequence of `add` and `move` calls within limits, `childList(p)`
returns a fresh array, and `node` is among its elements exactly when
`parent(node)` returns `p`. -/
theorem child_parent_source (before : Ariadne.State) (span : Span) (ops : List Operation)
    (runs : Runs «Tree##new» ops) (node p : JSString) :
    let address := before.heap.length + 2
    ∃ fresh list value after,
      SourceEvaluates Extracted_reference_tree.source before (.newClass "Tree" [] span) (.ref address) fresh ∧
      SourceTrace Extracted_reference_tree.source fresh
        (ops.map (call address) ++
          [(.method address "childList", [.string p]), (.method address "parent", [.string node])])
        (ops.map (fun _ => .undefined) ++ [.ref list, value]) after ∧
      ∃ children : List JSString, after.heap[list]? = some (.array (children.map .string)) ∧
        (node ∈ children ↔ value = .string p) := by
  intro address
  obtain ⟨fresh, constructed, layout⟩ := new_source before span
  obtain ⟨middle, trace, layout⟩ := trace_source fresh address _ _ _ ops runs layout
  let final := ops.foldl applyOp «Tree##new»
  obtain ⟨_, listed, listRun, ⟨list, rfl, fresher, array⟩, listLayout, _⟩ :=
    (childList_source middle address final _ _ p layout).elim
  obtain ⟨_, after, parentRun, rfl, _, keeps, _⟩ :=
    (parent_source listed address final _ _ node listLayout).elim
  have pBound := bound_of_some layout.parentsMap
  obtain ⟨_, cLookup, _⟩ := layout.childrenMap
  have cBound := bound_of_some cLookup
  have kept : after.heap[list]? = listed.heap[list]? :=
    keeps.2 list (bound_of_some array) (by omega) (by omega)
  refine ⟨fresh, list, _, after, constructed, trace.append
    (.next (Extracted_reference_tree.certificate.transfer_invocation listRun)
      (.next (Extracted_reference_tree.certificate.transfer_invocation parentRun) (.nil _))),
    «Tree#childList» final p, kept.trans array, ?_⟩
  rw [Examples.Proofs.ReferenceTree.child_parent_agree (reachable_fold ops _ .fresh)]
  cases «Tree#parent» final node with
  | none => simp
  | some q => simp [eq_comm]

end Examples.ReferenceSource.Tree
