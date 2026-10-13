import Examples.ReferenceSource.TreeBase

/-!
# The tree's `move`, transferred to its TypeScript source

`move` detaches a node from its old parent with a `filter` callback, walks up
from the new parent to rule out a cycle, and only then links the node under it.
-/

namespace Examples.ReferenceSource.Tree
open Ariadne Ariadne.Shallow Ariadne.Shallow.Adequacy Extracted_reference_tree.Shallow
open Heap

/-! ## `move` -/

def moveStmts : List Stmt :=
  match (method 3).body with
  | .block statements _ => statements
  | _ => []

/-- The parameters and body of the `filter` callback that drops `node` from the old parent's list. -/
def filterParts : List Param × Stmt :=
  match moveStmts with
  | [_, _, _, .if_ _ (.block [.expr (.call _ [_, .call _ [.lambda params body _] _] _) _] _) _ _, _, _, _, _] =>
    (params, body)
  | _ => default

/-- Unfold the parts of `move` named in a hypothesis into literal syntax. -/
syntax "unfold_move" ident : tactic
macro_rules
  | `(tactic| unfold_move $h) => `(tactic| simp only [filterParts, moveStmts, method, treeClass, P,
      Extracted_reference_tree.program, List.getElem!_cons_zero, List.getElem!_cons_succ, List.drop_succ_cons,
      List.drop_zero] at $h:ident)

/-- The callback, applied to each child, keeps exactly the children other than `node`. -/
theorem filter_traverse (captured : Env) (nodeLoc : Nat) (node : JSString)
    (capturedNode : captured.find? (fun p => p.1 == "node") = some ("node", nodeLoc)) :
    ∀ (xs : List JSString) (st : State) (clo idx : Nat),
      st.heap[clo]? = some (.closure filterParts.1 filterParts.2 captured) →
      st.heap[nodeLoc]? = some (.cell (.string node)) →
      WPTraverse P st (.ref clo) (xs.map .string) idx "filter" (fun results after =>
        results = (xs.filter (· != node)).map .string ∧ after.env = st.env ∧
        ∀ i, i < st.heap.length → after.heap[i]? = st.heap[i]?) := by
  intro xs
  induction xs with
  | nil => intro st clo idx _ _; exact WPTraverse.nil ⟨rfl, rfl, fun _ _ => rfl⟩
  | cons x xs ih =>
    intro st clo idx cloLookup nodeCell
    obtain ⟨hn, nodeCell'⟩ := getElem_of_some nodeCell
    have hclo := bound_of_some cloLookup
    have cloLookup' := cloLookup
    unfold_move cloLookup'
    refine WPTraverse.cons (WPI.closure cloLookup' ?_)
    twp
    refine ⟨Or.inr trivial, (ih _ clo (idx + 1) ?_ ?_).mono ?_⟩
    all_goals simp only [State.declare, State.alloc, List.zip_cons_cons, List.zip_nil_left, List.foldl_cons,
      List.foldl_nil] at *
    · first | exact cloLookup | (heap_simp; exact cloLookup)
    · first | exact nodeCell | (heap_simp; exact nodeCell)
    · intro ys after ⟨results, env, keep⟩
      refine ⟨?_, env, fun i hi => ?_⟩
      · by_cases same : x = node
        · subst same; simp [results]
        · simp [results, same]
      · rw [keep i (by first | omega | (simp; omega))]
        heap_simp

def optValue : Option JSString → Value
  | none => .undefined
  | some p => .string p

theorem mapGet_optValue (xs : List (JSString × JSString)) (k : JSString) :
    mapGet (stringStrings xs) (.string k) = optValue (MapEntries.get xs k) := by
  rw [mapGet_stringStrings]
  cases MapEntries.get xs k <;> rfl

def moveLoopParts : Expr × Stmt × Stmt :=
  match moveStmts with
  | [_, _, _, _, _, _, .for_ _ guard update body _, _] => (guard, update, body)
  | _ => default

/-- The loop state of `move`'s cycle check, above the heap `base` it began with. -/
structure MoveFrame (st : State) (base : Heap) (env0 : Env) (cursor : Option JSString) (k : Nat) : Prop where
  env : st.env = ("i", base.length + 1) :: ("cursor", base.length) :: env0
  keep : ∀ i, i < base.length → st.heap[i]? = base[i]?
  long : base.length + 2 ≤ st.heap.length
  cursorCell : st.heap[base.length]? = some (.cell (optValue cursor))
  iCell : st.heap[base.length + 1]? = some (.cell (.number (Float.Model.ofInt k)))

theorem move_loop (base : Heap) (address : Nat) (d : State') (pA cA : Nat)
    (input : Layout base address d pA cA) (enc : List (Value × Value))
    (cLookup : base[cA]? = some (.map enc)) (len : enc.length = d.children.size)
    (range : Int53.InRange (d.children.size : Int)) (n oL : Nat) (node : JSString) (parent : Value)
    (thisCell : base[n]? = some (.cell (.ref address))) (nodeCell : base[n + 1]? = some (.cell (.string node))) :
    ∀ m k cursor st, k + m = d.children.size →
      MoveFrame st base [("old", oL), ("parent", n + 2), ("node", n + 1), ("this", n)] cursor k →
      WPLoop P st moveLoopParts.1 moveLoopParts.2.2 (some moveLoopParts.2.1) (fun out =>
        (∀ i, i < base.length → out.state.heap[i]? = base[i]?) ∧
        ((Examples.Proofs.ReferenceTree.hits d node m cursor = true ∧ out.control = .returned ∧
            out.value = .undefined) ∨
         (Examples.Proofs.ReferenceTree.hits d node m cursor = false ∧ out.control = .normal ∧
            out.state.env = st.env))) := by
  have hl0 := bound_of_some thisCell
  have hl1 := bound_of_some nodeCell
  obtain ⟨_, thisCell'⟩ := getElem_of_some thisCell
  obtain ⟨_, nodeCell'⟩ := getElem_of_some nodeCell
  intro m
  induction m with
  | zero =>
    intro k cursor st count frame
    have henv := frame.env
    have long := frame.long
    obtain ⟨hl3, iCell⟩ := getElem_of_some frame.iCell
    have inst := (frame.keep address (bound_of_some input.instance_)).trans input.instance_
    obtain ⟨ha, inst⟩ := getElem_of_some inst
    have cMap := (frame.keep cA (bound_of_some cLookup)).trans cLookup
    obtain ⟨hc, cMap⟩ := getElem_of_some cMap
    have stop : ¬ (Float.Model.ofInt (k : Int) < Float.Model.ofNat d.children.size) := by
      rw [ofNat_ofInt, Int53.lt_ofInt _ _ (nat_range (by omega) range) range]
      omega
    have this' := (frame.keep n hl0).trans thisCell
    obtain ⟨_, this''⟩ := getElem_of_some this'
    conv => arg 3; simp only [moveLoopParts, moveStmts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    conv => arg 4; simp only [moveLoopParts, moveStmts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    conv => arg 5; simp only [moveLoopParts, moveStmts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    refine WPLoop.step ?_
    twp
    exact ⟨frame.keep, Or.inr ⟨rfl, trivial, trivial⟩⟩
  | succ m ih =>
    intro k cursor st count frame
    have henv := frame.env
    have long := frame.long
    obtain ⟨hl3, iCell⟩ := getElem_of_some frame.iCell
    have inst := (frame.keep address (bound_of_some input.instance_)).trans input.instance_
    obtain ⟨ha, inst⟩ := getElem_of_some inst
    have cMap := (frame.keep cA (bound_of_some cLookup)).trans cLookup
    obtain ⟨hc, cMap⟩ := getElem_of_some cMap
    have pMap := (frame.keep pA (bound_of_some input.parentsMap)).trans input.parentsMap
    obtain ⟨hp, pMap⟩ := getElem_of_some pMap
    have go : Float.Model.ofInt (k : Int) < Float.Model.ofNat d.children.size := by
      rw [ofNat_ofInt, Int53.lt_ofInt _ _ (nat_range (by omega) range) range]
      omega
    have this' := (frame.keep n hl0).trans thisCell
    obtain ⟨_, this''⟩ := getElem_of_some this'
    have node' := (frame.keep (n + 1) hl1).trans nodeCell
    obtain ⟨_, node''⟩ := getElem_of_some node'
    have cursorCell := frame.cursorCell
    obtain ⟨hl2, cursorCell'⟩ := getElem_of_some cursorCell
    have step : Float.Model.ofInt (k : Int) + Float.Model.ofScientific 1 0 = Float.Model.ofInt ((k + 1 : Nat) : Int) := by
      rw [one_scientific, ← Int53.add_exact _ _ (nat_range (by omega) range) (by decide)
        (by exact_mod_cast nat_range (by omega) range)]
      rfl
    conv => arg 3; simp only [moveLoopParts, moveStmts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    conv => arg 4; simp only [moveLoopParts, moveStmts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    conv => arg 5; simp only [moveLoopParts, moveStmts, method, treeClass, P, Extracted_reference_tree.program,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    refine WPLoop.step ?_
    cases cursor with
    | none =>
      simp only [optValue] at cursorCell cursorCell'
      twp
      exact ⟨frame.keep, Or.inr ⟨rfl, trivial, trivial⟩⟩
    | some p =>
      simp only [optValue] at cursorCell cursorCell'
      by_cases same : p = node
      · subst same
        twp
        exact ⟨frame.keep, Or.inl ⟨by simp [Examples.Proofs.ReferenceTree.hits], trivial, trivial⟩⟩
      · have ne : (p == node) = false := by simpa using same
        have pget := mapGet_optValue d.parents.entries p
        twp
        have hits : Examples.Proofs.ReferenceTree.hits d node (m + 1) (some p) =
            Examples.Proofs.ReferenceTree.hits d node m (d.parents.get p) := by
          simp [Examples.Proofs.ReferenceTree.hits, same]
        rw [hits]
        refine (ih (k + 1) (d.parents.get p) _ (by omega) ⟨rfl, fun i hi => ?_, ?_, ?_, ?_⟩).mono ?_
        · heap_simp
          exact frame.keep i hi
        · simp only [List.length_set]; omega
        · heap_simp; rfl
        · heap_simp; simp
        · intro out ⟨keep, h⟩
          exact ⟨keep, h⟩

/-- What `move` leaves: no value, the final state's layout, and every other object kept. -/
def MovePost (heap0 : Heap) (address pA cA : Nat) (final : State') (out : Completion) : Prop :=
  (out.control = .normal ∨ out.control = .returned) ∧ out.value = .undefined ∧
    Layout out.state.heap address final pA cA ∧ Keeps heap0 out.state.heap pA cA

set_option maxHeartbeats 2000000 in
/-- Statements six to eight of `move`: the cycle check, then the new parent link. -/
theorem move_tail (heap0 : Heap) (st : State) (address : Nat) (d : State') (pA cA : Nat) (node : JSString)
    (parent : Option JSString) (oL : Nat)
    (input : Layout st.heap address d pA cA) (kept : Keeps heap0 st.heap pA cA)
    (below : pA < heap0.length ∧ cA < heap0.length)
    (range : Int53.InRange (d.children.size : Int))
    (fits : ∀ p, parent = some p → ((d.children.get p).getD []).length + 1 < 4294967296)
    (env : st.env = [("old", oL), ("parent", heap0.length + 2), ("node", heap0.length + 1), ("this", heap0.length)])
    (thisCell : st.heap[heap0.length]? = some (.cell (.ref address)))
    (nodeCell : st.heap[heap0.length + 1]? = some (.cell (.string node)))
    (parentCell : st.heap[heap0.length + 2]? = some (.cell (optValue parent))) :
    WPB P st (moveStmts.drop 5) (MovePost heap0 address pA cA
      (if Examples.Proofs.ReferenceTree.hits d node d.children.size parent then d
       else Examples.Proofs.ReferenceTree.after d node parent)) := by
  obtain ⟨enc, cLookup, children⟩ := input.childrenMap
  have loop := move_loop st.heap address d pA cA input enc cLookup children.length range heap0.length oL node
    (optValue parent) thisCell nodeCell d.children.size 0 parent
  simp only [moveLoopParts, moveStmts, method, treeClass, P, Extracted_reference_tree.program,
    List.getElem!_cons_zero, List.getElem!_cons_succ] at loop
  obtain ⟨hn0, thisCell'⟩ := getElem_of_some thisCell
  obtain ⟨hn1, nodeCell'⟩ := getElem_of_some nodeCell
  obtain ⟨hn2, parentCell'⟩ := getElem_of_some parentCell
  conv => arg 3; simp only [moveStmts, method, treeClass, P, Extracted_reference_tree.program,
    List.getElem!_cons_zero, List.getElem!_cons_succ, List.drop_succ_cons, List.drop_zero]
  twp
  refine WPS.for_ ?_
  twp
  rw [zero_scientific]
  refine (loop _ (by simp) ⟨?_, fun i hi => ?_, ?_, ?_, ?_⟩).mono ?_
  all_goals try simp only [State.declare, State.alloc]
  all_goals try heap_simp
  · rw [env]
  · omega
  · rfl
  intro out ⟨keep, finished⟩
  have keeps : Keeps heap0 out.state.heap pA cA := kept.trans (Keeps.of_agree (length_le_of_agree keep) keep)
  have layout := input.extend keep
  rcases finished with ⟨hit, ret, value⟩ | ⟨miss, normal, outEnv⟩
  · rw [if_neg (by simp [ret]), hit, if_pos rfl]
    exact ⟨Or.inr ret, value, layout, keeps⟩
  · rw [if_pos normal, miss]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have parentCell2 := (keep _ hn2).trans parentCell
    cases parent with
    | none =>
      simp only [optValue] at parentCell2
      obtain ⟨_, parentCell3⟩ := getElem_of_some parentCell2
      twp
      exact ⟨Or.inl rfl, rfl, layout, keeps⟩
    | some p =>
      simp only [optValue] at parentCell2
      obtain ⟨_, parentCell3⟩ := getElem_of_some parentCell2
      obtain ⟨_, thisCell2⟩ := getElem_of_some ((keep _ hn0).trans thisCell)
      obtain ⟨_, nodeCell2⟩ := getElem_of_some ((keep _ hn1).trans nodeCell)
      obtain ⟨ha, inst⟩ := getElem_of_some layout.instance_
      obtain ⟨hp, pMap⟩ := getElem_of_some layout.parentsMap
      obtain ⟨enc', cLookup', children'⟩ := layout.childrenMap
      obtain ⟨hc, cMap⟩ := getElem_of_some cLookup'
      obtain ⟨d1, d2, d3⟩ := layout.distinct
      have e1 := Ne.symm d1; have e2 := Ne.symm d2; have e3 := Ne.symm d3
      have f0 : pA ≠ heap0.length := by omega
      have f1 : pA ≠ heap0.length + 1 := by omega
      have f2 : pA ≠ heap0.length + 2 := by omega
      have g0 : cA ≠ heap0.length := by omega
      have g1 : cA ≠ heap0.length + 1 := by omega
      have g2 : cA ≠ heap0.length + 2 := by omega
      cases seen : MapEntries.get d.children.entries p with
      | some v =>
        obtain ⟨a, mg, lookup, na, nc⟩ := children'.get_some seen
        have na' := Ne.symm na; have nc' := Ne.symm nc
        obtain ⟨hla, arr⟩ := getElem_of_some lookup
        have fit := fits p rfl
        simp only [JSMap.get, seen, Option.getD_some] at fit
        twp
        have attached : Examples.Proofs.ReferenceTree.after d node (some p) =
            { parents := d.parents.set node p, children := d.children.set p (v ++ [node]) } := by
          simp [Examples.Proofs.ReferenceTree.after, Examples.Proofs.ReferenceTree.attached, JSMap.get, seen]
        rw [attached]
        simp only [State.alloc, List.length_set]
        refine ⟨Or.inl rfl, rfl, layout.rewrite _ (fun i hi np nc => ?_) ?_
          ⟨_, ?_, Children.set (a := out.state.heap.length) ?_ ?_ ?_ (children'.mono (fun i hi np nc => ?_))⟩,
          keeps.trans ⟨by simp, fun i hi np nc => ?_⟩⟩
        all_goals heap_simp
        all_goals first | omega | simp [JSMap.set, stringStrings, mapSet_string]
      | none =>
        have mg := children'.get_none seen
        twp
        have attached : Examples.Proofs.ReferenceTree.after d node (some p) =
            { parents := d.parents.set node p, children := d.children.set p [node] } := by
          simp [Examples.Proofs.ReferenceTree.after, Examples.Proofs.ReferenceTree.attached, JSMap.get, seen]
        rw [attached]
        simp only [State.alloc, List.length_set, List.length_append, List.length_cons, List.length_nil,
          List.nil_append, Nat.zero_add]
        refine ⟨Or.inl rfl, rfl, layout.rewrite _ (fun i hi np nc => ?_) ?_
          ⟨_, ?_, Children.set (a := out.state.heap.length + 1) ?_ ?_ ?_ (children'.mono (fun i hi np nc => ?_))⟩,
          keeps.trans ⟨by simp, fun i hi np nc => ?_⟩⟩
        all_goals heap_simp
        all_goals first | omega | simp [JSMap.set, stringStrings, mapSet_string]

/-- The last three statements of `move`, kept opaque so stepping stops in front of them. -/
def moveTail : List Stmt := moveStmts.drop 5
theorem moveTail_eq : moveTail = moveStmts.drop 5 := rfl
attribute [irreducible] moveTail

theorem drop_two : moveStmts.drop 2 = moveStmts[2]! :: moveStmts[3]! :: moveStmts[4]! :: moveTail := by
  rw [moveTail_eq]; kernel_rfl

set_option maxHeartbeats 2000000 in
/-- Statements three to five of `move`: detach the node from its old parent. -/
theorem move_middle (heap0 : Heap) (st : State) (address : Nat) (a : State') (pA cA : Nat) (node : JSString)
    (parent : Option JSString)
    (input : Layout st.heap address a pA cA) (kept : Keeps heap0 st.heap pA cA)
    (below : pA < heap0.length ∧ cA < heap0.length)
    (range : Int53.InRange ((Examples.Proofs.ReferenceTree.detached a node).children.size : Int))
    (fits : ∀ p, parent = some p →
      (((Examples.Proofs.ReferenceTree.detached a node).children.get p).getD []).length + 1 < 4294967296)
    (env : st.env = [("parent", heap0.length + 2), ("node", heap0.length + 1), ("this", heap0.length)])
    (thisCell : st.heap[heap0.length]? = some (.cell (.ref address)))
    (nodeCell : st.heap[heap0.length + 1]? = some (.cell (.string node)))
    (parentCell : st.heap[heap0.length + 2]? = some (.cell (optValue parent))) :
    WPB P st (moveStmts.drop 2) (MovePost heap0 address pA cA
      (let d := Examples.Proofs.ReferenceTree.detached a node
       if Examples.Proofs.ReferenceTree.hits d node d.children.size parent then d
       else Examples.Proofs.ReferenceTree.after d node parent)) := by
  layout_facts
  obtain ⟨hn0, thisCell'⟩ := getElem_of_some thisCell
  obtain ⟨hn1, nodeCell'⟩ := getElem_of_some nodeCell
  obtain ⟨hn2, parentCell'⟩ := getElem_of_some parentCell
  have f0 : pA ≠ heap0.length := by omega
  have f1 : pA ≠ heap0.length + 1 := by omega
  have f2 : pA ≠ heap0.length + 2 := by omega
  have g0 : cA ≠ heap0.length := by omega
  have g1 : cA ≠ heap0.length + 1 := by omega
  have g2 : cA ≠ heap0.length + 2 := by omega
  have pget := mapGet_optValue a.parents.entries node
  rw [drop_two]
  conv => arg 3; simp only [moveStmts, method, treeClass, P, Extracted_reference_tree.program,
    List.getElem!_cons_zero, List.getElem!_cons_succ]
  cases up : MapEntries.get a.parents.entries node with
  | none =>
    simp only [up, optValue] at pget
    twp
    rw [moveTail_eq]
    have det : Examples.Proofs.ReferenceTree.detached a node = { a with parents := a.parents.delete node } := by
      simp [Examples.Proofs.ReferenceTree.detached, JSMap.get, up]
    refine move_tail heap0 _ address _ pA cA node parent st.heap.length ?_ ?_ below range fits ?_ ?_ ?_ ?_
    · rw [det]
      refine input.rewrite _ (fun i hi np nc => ?_) ?_ ⟨enc, ?_, children.mono (fun i hi np nc => ?_)⟩
      all_goals simp only [State.declare, State.alloc]
      all_goals heap_simp
      all_goals first | omega | simp [JSMap.delete, stringStrings, mapDelete_string]
    · refine kept.trans ⟨by simp [State.declare, State.alloc], fun i hi np nc => ?_⟩
      simp only [State.declare, State.alloc]
      heap_simp
    · simp [State.declare, State.alloc, env]
    all_goals simp only [State.declare, State.alloc]
    all_goals heap_simp
    all_goals first | omega | simp [*]
  | some o =>
    simp only [up, optValue] at pget
    cases seen : MapEntries.get a.children.entries o with
    | some v =>
      obtain ⟨arr, mg, lookup, na, nc⟩ := children.get_some seen
      have na' := Ne.symm na; have nc' := Ne.symm nc
      obtain ⟨hla, arr'⟩ := getElem_of_some lookup
      twp
      have ft := filter_traverse (st.declare "old" (.string o)).env (heap0.length + 1) node
        (by simp [State.declare, State.alloc, env]) v
      unfold_move ft
      refine (ft _ _ 0 ?_ ?_).mono ?_
      · simp only [State.declare, State.alloc]
        heap_simp
      · simp only [State.declare, State.alloc]
        heap_simp
        exact nodeCell
      rintro results after ⟨rfl, env', keep'⟩
      simp only [State.declare, State.alloc, List.length_append, List.length_cons, List.length_nil] at keep' env'
      have kc := keep' cA (by omega)
      have kp := keep' pA (by omega)
      have k0 := keep' heap0.length (by omega)
      have k1 := keep' (heap0.length + 1) (by omega)
      have k2 := keep' (heap0.length + 2) (by omega)
      have ka := keep' address (by omega)
      heap_simp
      rw [cLookup] at kc
      rw [input.parentsMap] at kp
      rw [thisCell] at k0
      rw [nodeCell] at k1
      rw [parentCell] at k2
      rw [input.instance_] at ka
      obtain ⟨_, kc'⟩ := getElem_of_some kc
      obtain ⟨_, kp'⟩ := getElem_of_some kp
      obtain ⟨_, k0'⟩ := getElem_of_some k0
      obtain ⟨_, k1'⟩ := getElem_of_some k1
      obtain ⟨_, k2'⟩ := getElem_of_some k2
      obtain ⟨_, ka'⟩ := getElem_of_some ka
      twp
      rw [moveTail_eq]
      have det : Examples.Proofs.ReferenceTree.detached a node =
          { parents := a.parents.delete node, children := a.children.set o (v.filter (· != node)) } := by
        simp [Examples.Proofs.ReferenceTree.detached, JSMap.get, up, seen]
      have longer : st.heap.length + 2 ≤ after.heap.length := by
        have kl := keep' (st.heap.length + 1) (by omega)
        rw [List.getElem?_append_right (by simp)] at kl
        simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_cons_zero] at kl
        have := bound_of_some kl
        omega
      refine move_tail heap0 _ address _ pA cA node parent st.heap.length ?_ ?_ below range fits ?_ ?_ ?_ ?_
      · rw [det]
        refine input.rewrite _ (fun i hi np nc => ?_) ?_
          ⟨_, ?_, Children.set (a := after.heap.length) ?_ ?_ ?_ (children.mono (fun i hi np nc => ?_))⟩
        all_goals try simp only [State.alloc]
        all_goals try heap_simp
        all_goals try (rw [keep' i (by omega)]; heap_simp)
        all_goals first | omega | simp [JSMap.delete, JSMap.set, stringStrings, mapDelete_string]
      · refine kept.trans ⟨by simp [State.alloc]; omega, fun i hi np nc => ?_⟩
        simp only [State.alloc]
        heap_simp
        rw [keep' i (by omega)]
        heap_simp
      · simp [State.declare, State.alloc, env]
      all_goals try simp only [State.alloc]
      all_goals heap_simp
      all_goals first | omega | simp [*]
    | none =>
      have mg := children.get_none seen
      twp
      have ft := filter_traverse (st.declare "old" (.string o)).env (heap0.length + 1) node
        (by simp [State.declare, State.alloc, env]) []
      unfold_move ft
      refine (ft _ _ 0 ?_ ?_).mono ?_
      · simp only [State.declare, State.alloc]
        heap_simp
      · simp only [State.declare, State.alloc]
        heap_simp
        exact nodeCell
      rintro results after ⟨rfl, env', keep'⟩
      simp only [State.declare, State.alloc, List.length_append, List.length_cons, List.length_nil] at keep' env'
      have kc := keep' cA (by omega)
      have kp := keep' pA (by omega)
      have k0 := keep' heap0.length (by omega)
      have k1 := keep' (heap0.length + 1) (by omega)
      have k2 := keep' (heap0.length + 2) (by omega)
      have ka := keep' address (by omega)
      heap_simp
      rw [cLookup] at kc
      rw [input.parentsMap] at kp
      rw [thisCell] at k0
      rw [nodeCell] at k1
      rw [parentCell] at k2
      rw [input.instance_] at ka
      obtain ⟨_, kc'⟩ := getElem_of_some kc
      obtain ⟨_, kp'⟩ := getElem_of_some kp
      obtain ⟨_, k0'⟩ := getElem_of_some k0
      obtain ⟨_, k1'⟩ := getElem_of_some k1
      obtain ⟨_, k2'⟩ := getElem_of_some k2
      obtain ⟨_, ka'⟩ := getElem_of_some ka
      twp
      rw [moveTail_eq]
      have det : Examples.Proofs.ReferenceTree.detached a node =
          { parents := a.parents.delete node, children := a.children.set o [] } := by
        simp [Examples.Proofs.ReferenceTree.detached, JSMap.get, up, seen]
      have longer : st.heap.length + 3 ≤ after.heap.length := by
        have kl := keep' (st.heap.length + 2) (by omega)
        rw [List.getElem?_append_right (by simp)] at kl
        simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_cons_zero] at kl
        have := bound_of_some kl
        omega
      refine move_tail heap0 _ address _ pA cA node parent st.heap.length ?_ ?_ below range fits ?_ ?_ ?_ ?_
      · rw [det]
        refine input.rewrite _ (fun i hi np nc => ?_) ?_
          ⟨_, ?_, Children.set (a := after.heap.length) ?_ ?_ ?_ (children.mono (fun i hi np nc => ?_))⟩
        all_goals try simp only [State.alloc]
        all_goals try heap_simp
        all_goals try (rw [keep' i (by omega)]; heap_simp)
        all_goals first | omega | simp [JSMap.delete, JSMap.set, stringStrings, mapDelete_string]
      · refine kept.trans ⟨by simp [State.alloc]; omega, fun i hi np nc => ?_⟩
        simp only [State.alloc]
        heap_simp
        rw [keep' i (by omega)]
        heap_simp
      · simp [State.declare, State.alloc, env]
      all_goals try simp only [State.alloc]
      all_goals heap_simp
      all_goals first | omega | simp [*]

/-- Statements three onwards, kept opaque so stepping stops in front of them. -/
def moveRest : List Stmt := moveStmts.drop 2
theorem moveRest_eq : moveRest = moveStmts.drop 2 := rfl
attribute [irreducible] moveRest

def moveSpan : Span :=
  match (method 3).body with
  | .block _ span => span
  | _ => default

theorem moveBody : (method 3).body = .block (moveStmts[0]! :: moveStmts[1]! :: moveRest) moveSpan := by
  rw [moveRest_eq]; kernel_rfl

/-- The heap cells of `move`'s three bindings, kept by a nested call that only rewrites the maps. -/
theorem cells_keep {heap heap' : Heap} {pA cA n : Nat} (keeps : Keeps heap heap' pA cA)
    (np : pA < n) (nc : cA < n) {i : Nat} (hi : n ≤ i) (bound : i < heap.length) : heap'[i]? = heap[i]? :=
  keeps.2 i bound (by omega) (by omega)

set_option maxHeartbeats 2000000 in
theorem move_source (before : State) (address : Nat) (native : State') (pA cA : Nat) (node : JSString)
    (parent : Option JSString) (input : Layout before.heap address native pA cA)
    (range : Int53.InRange ((Examples.Proofs.ReferenceTree.detached
      (parent.elim (Examples.Proofs.ReferenceTree.add native node)
        (Examples.Proofs.ReferenceTree.add (Examples.Proofs.ReferenceTree.add native node))) node).children.size : Int))
    (fits : ∀ p, parent = some p →
      (((Examples.Proofs.ReferenceTree.detached
        (parent.elim (Examples.Proofs.ReferenceTree.add native node)
          (Examples.Proofs.ReferenceTree.add (Examples.Proofs.ReferenceTree.add native node))) node).children.get p).getD
        []).length + 1 < 4294967296) :
    WPI P before (.method address "move") [.string node, optValue parent] (fun result after =>
      result = .undefined ∧ Layout after.heap address (Examples.Proofs.ReferenceTree.move native node parent) pA cA ∧
      Keeps before.heap after.heap pA cA ∧ after.env = before.env) := by
  layout_facts
  change WPI P before (.method address (method 3).name) _ _
  refine WPI.method (class_ := treeClass) (by rw [treeName]; exact input.instance_) treeFind (methodFind 3) ?_
  rw [moveBody]
  conv => arg 2; simp only [method, treeClass, P, Extracted_reference_tree.program,
    List.getElem!_cons_zero, List.getElem!_cons_succ]
  conv => arg 3; simp only [moveStmts, method, treeClass, P, Extracted_reference_tree.program,
    List.getElem!_cons_zero, List.getElem!_cons_succ]
  twp
  have below : pA < before.heap.length ∧ cA < before.heap.length := ⟨hp, hc⟩
  refine (add_source _ address native pA cA node (input.extend (fun i hi => ?_))).mono ?_
  · simp [bindArguments, State.declare, State.alloc, List.getElem?_append_left hi]
  rintro _ s1 ⟨-, l1, k1, e1⟩
  simp only [bindArguments, State.declare, State.alloc, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
    List.foldl_nil, List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at k1 e1
  have kept1 : Keeps before.heap s1.heap pA cA :=
    (Keeps.of_agree (by simp) (fun i hi => by heap_simp)).trans k1
  have c0 : s1.heap[before.heap.length]? = some (.cell (.ref address)) := by
    rw [k1.2 _ (by simp) (by omega) (by omega)]; heap_simp
  have c1 : s1.heap[before.heap.length + 1]? = some (.cell (.string node)) := by
    rw [k1.2 _ (by simp) (by omega) (by omega)]; heap_simp
  have c2 : s1.heap[before.heap.length + 2]? = some (.cell (optValue parent)) := by
    rw [k1.2 _ (by simp) (by omega) (by omega)]; heap_simp
  have finish : ∀ a : State', ∀ s : State, ∀ final : State',
      final = Examples.Proofs.ReferenceTree.move native node parent →
      WPB P s moveRest (MovePost before.heap address pA cA final) →
      WPB P s moveRest (fun out => (out.control = .normal ∨ out.control = .returned) ∧
        out.value = .undefined ∧ Layout out.state.heap address (Examples.Proofs.ReferenceTree.move native node parent) pA cA ∧
        Keeps before.heap out.state.heap pA cA ∧ True) := by
    intro _ s final same h
    subst same
    exact h.mono (fun out ⟨ctrl, val, lay, keeps⟩ => ⟨ctrl, val, lay, keeps, trivial⟩)
  obtain ⟨_, c0'⟩ := getElem_of_some c0
  obtain ⟨_, c1'⟩ := getElem_of_some c1
  obtain ⟨_, c2'⟩ := getElem_of_some c2
  obtain ⟨_, inst1⟩ := getElem_of_some l1.instance_
  cases parent with
  | none =>
    simp only [optValue] at c2 c2'
    twp
    refine finish (Examples.Proofs.ReferenceTree.add native node) _ _ rfl ?_
    rw [moveRest_eq]
    exact move_middle before.heap _ address _ pA cA node none l1 kept1 below range fits (by simpa using e1)
      c0 c1 c2
  | some p =>
    simp only [optValue] at c2 c2'
    twp
    refine (add_source _ address _ pA cA p l1).mono ?_
    rintro _ s2 ⟨-, l2, k2, e2⟩
    have kept2 := kept1.trans k2
    have d0 : s2.heap[before.heap.length]? = some (.cell (.ref address)) := by
      rw [k2.2 _ (bound_of_some c0) (by omega) (by omega)]; exact c0
    have d1 : s2.heap[before.heap.length + 1]? = some (.cell (.string node)) := by
      rw [k2.2 _ (bound_of_some c1) (by omega) (by omega)]; exact c1
    have d2 : s2.heap[before.heap.length + 2]? = some (.cell (optValue (some p))) := by
      rw [k2.2 _ (bound_of_some c2) (by omega) (by omega)]; exact c2
    twp
    refine finish native _ _ rfl ?_
    rw [moveRest_eq]
    exact move_middle before.heap _ address _ pA cA node (some p) l2 kept2 below range fits
      (by simp) d0 d1 d2

end Examples.ReferenceSource.Tree
