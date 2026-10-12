import Examples.ShallowReference.tree
namespace Examples.Proofs.ReferenceTree
open Ariadne Ariadne.Shallow Extracted_reference_tree.Shallow
abbrev State := NativeTypes.«Tree#state»
def walk (s : State) : Nat → JSString → JSString
  | 0, node => node
  | n + 1, node => match s.parents.get node with
    | none => node
    | some parent => walk s n parent

private theorem root_loop (xs : List Int) (s : State) (node cursor : JSString) :
    Exit.elim (Loop.each xs (Loop.integers, (cursor, (s, (node, ())))) JoinNative.«Tree#root#1»)
      JoinNative.«Tree#root#2» id = walk s xs.length cursor := by
  induction xs generalizing cursor with
  | nil => rfl
  | cons x xs ih =>
    cases h : s.parents.get cursor
    all_goals simp [Loop.each, walk, h, Exit.elim]
    exact ih _

theorem root_eq (s : State) (node : JSString) :
    «Tree#root» s node = walk s s.children.size node := by
  unfold «Tree#root»
  change Exit.elim (Loop.each (Loop.integers 0 (Int.ofNat s.children.size))
    (Loop.integers, (node, (s, (node, ())))) JoinNative.«Tree#root#1») JoinNative.«Tree#root#2» id = _
  rw [root_loop]
  simp

theorem parent_eq (s : State) (node : JSString) : «Tree#parent» s node = s.parents.get node := rfl

theorem childList_eq (s : State) (node : JSString) :
    «Tree#childList» s node = (s.children.get node).getD [] := by
  cases h : s.children.get node <;> simp [«Tree#childList», h]

/-- A parent edge strictly reduces rank; this excludes cycles. -/
def Ranked (s : State) (rank : JSString → Nat) : Prop :=
  ∀ node parent, s.parents.get node = some parent → rank parent < rank node

theorem walk_finishes (s : State) (rank : JSString → Nat) (ranked : Ranked s rank)
    (n : Nat) (node : JSString) (enough : rank node ≤ n) :
    s.parents.get (walk s n node) = none := by
  induction n generalizing node with
  | zero =>
    cases h : s.parents.get node with
    | none => exact h
    | some parent => have := ranked node parent h; omega
  | succ n ih =>
    cases h : s.parents.get node with
    | none => simp [walk, h]
    | some parent =>
      have := ranked node parent h
      simpa [walk, h] using ih parent (by omega)

def chain (s : State) : Nat → JSString → List JSString
  | 0, _ => []
  | n + 1, node => node :: (match s.parents.get node with
    | none => []
    | some parent => chain s n parent)

theorem chain_rank (s : State) (rank : JSString → Nat) (ranked : Ranked s rank)
    (n : Nat) (node x : JSString) (member : x ∈ chain s n node) : rank x ≤ rank node := by
  induction n generalizing node with
  | zero => simp [chain] at member
  | succ n ih =>
    simp only [chain, List.mem_cons] at member
    rcases member with rfl | member
    · exact Nat.le_refl _
    · cases h : s.parents.get node with
      | none => simp [h] at member
      | some parent =>
        simp only [h] at member
        have := ih parent member
        have := ranked node parent h
        omega

theorem chain_nodup (s : State) (rank : JSString → Nat) (ranked : Ranked s rank)
    (n : Nat) (node : JSString) : (chain s n node).Nodup := by
  induction n generalizing node with
  | zero => simp [chain]
  | succ n ih =>
    cases h : s.parents.get node with
    | none => simp [chain, h]
    | some parent =>
      simp only [chain, h, List.nodup_cons]
      refine ⟨?_, ih parent⟩
      intro member
      have := chain_rank s rank ranked n parent node member
      have := ranked node parent h
      omega

/-- All parent endpoints are registered nodes. -/
def Closed (s : State) : Prop := ∀ node parent, s.parents.get node = some parent →
  node ∈ s.children.keys ∧ parent ∈ s.children.keys

theorem chain_subset (s : State) (closed : Closed s) (n : Nat) (node : JSString)
    (known : node ∈ s.children.keys) : chain s n node ⊆ s.children.keys := by
  induction n generalizing node with
  | zero => simp [chain]
  | succ n ih =>
    intro x hx
    simp only [chain, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact known
    · cases h : s.parents.get node with
      | none => simp [h] at hx
      | some parent => exact ih parent (closed node parent h).2 (by simpa [h] using hx)

theorem walk_rooted (s : State) (node : JSString) (root : s.parents.get node = none) (n : Nat) :
    walk s n node = node := by
  cases n <;> simp [walk, root]

theorem walk_add (s : State) (n m : Nat) (node : JSString) :
    walk s (n + m) node = walk s m (walk s n node) := by
  induction n generalizing node with
  | zero => simp [walk]
  | succ n ih =>
    cases h : s.parents.get node with
    | none => simp [walk, h, walk_rooted s node h]
    | some parent => simpa [Nat.succ_add, walk, h] using ih parent

theorem chain_finishes (s : State) (rank : JSString → Nat) (ranked : Ranked s rank)
    (n : Nat) (node : JSString) (enough : rank node < n) :
    s.parents.get (walk s (chain s n node).length node) = none := by
  induction n generalizing node with
  | zero => omega
  | succ n ih =>
    cases h : s.parents.get node with
    | none => simp [chain, walk, h]
    | some parent =>
      have := ranked node parent h
      simpa [chain, walk, h] using ih parent (by omega)

theorem root_reached (s : State) (rank : JSString → Nat) (ranked : Ranked s rank)
    (closed : Closed s) (node : JSString) : «Tree#parent» s («Tree#root» s node) = none := by
  rw [parent_eq, root_eq]
  by_cases known : node ∈ s.children.keys
  · let path := chain s (rank node + 1) node
    have bound : path.length ≤ s.children.size := by
      have h := (chain_nodup s rank ranked (rank node + 1) node).length_le_of_subset
        (chain_subset s closed (rank node + 1) node known)
      simpa [JSMap.keys, JSMap.size, path] using h
    have root := chain_finishes s rank ranked (rank node + 1) node (by omega)
    have count : s.children.size = path.length + (s.children.size - path.length) := by omega
    rw [count, walk_add, walk_rooted s _ root]
    exact root
  · have root : s.parents.get node = none := by
      cases h : s.parents.get node with
      | none => rfl
      | some parent => exact False.elim (known (closed node parent h).1)
    rw [walk_rooted s node root]
    exact root

def add (s : State) (node : JSString) : State :=
  if s.children.has node then s else { s with children := s.children.set node [] }

theorem add_eq (s : State) (node : JSString) : («Tree#add» s node).2.1 = add s node := by
  unfold «Tree#add» add
  split <;> simp_all

def detached (s : State) (node : JSString) : State :=
  { parents := s.parents.delete node
    children := match s.parents.get node with
      | none => s.children
      | some old => s.children.set old ((s.children.get old).getD [] |>.filter (· != node)) }

def attached (s : State) (node parent : JSString) : State :=
  { parents := s.parents.set node parent
    children := s.children.set parent ((s.children.get parent).getD [] ++ [node]) }

/-- Child membership agrees exactly with parent lookup. -/
def Consistent (s : State) : Prop := ∀ node parent,
  node ∈ (s.children.get parent).getD [] ↔ s.parents.get node = some parent

theorem add_consistent (s : State) (consistent : Consistent s) (node : JSString) :
    Consistent (add s node) := by
  intro x p
  unfold add
  split
  · exact consistent x p
  · rename_i absent
    have absentGet : s.children.get node = none := by
      cases h : s.children.get node <;> simp_all [JSMap.has]
    by_cases same : node = p
    · subst p
      have old := consistent x node
      simp [absentGet] at old
      simpa using old
    · simpa [JSMap.get_set, same] using consistent x p

theorem detached_consistent (s : State) (consistent : Consistent s) (node : JSString) :
    Consistent (detached s node) := by
  intro x p
  cases h : s.parents.get node with
  | none =>
    by_cases same : node = x
    · subst x; simpa [detached, h] using consistent node p
    · simpa [detached, h, JSMap.get_delete, same] using consistent x p
  | some old =>
    by_cases same : node = x
    · subst x
      by_cases parent : old = p
      · subst p; simp [detached, h]
      · have old := consistent node p
        simpa [detached, h, JSMap.get_delete, JSMap.get_set, parent] using old
    · by_cases parent : old = p
      · subst p
        simpa [detached, h, JSMap.get_delete, JSMap.get_set, same, Ne.symm same] using consistent x old
      · simpa [detached, h, JSMap.get_delete, JSMap.get_set, same, parent] using consistent x p

theorem attached_consistent (s : State) (consistent : Consistent s) (node parent : JSString)
    (free : s.parents.get node = none) : Consistent (attached s node parent) := by
  intro x p
  by_cases same : node = x
  · subst x
    have old := consistent node p
    simp [free] at old
    by_cases hp : parent = p <;> simp [attached, JSMap.get_set, hp, old]
  · by_cases hp : parent = p
    · subst p
      simpa [attached, JSMap.get_set, same, Ne.symm same] using consistent x parent
    · simpa [attached, JSMap.get_set, same, hp] using consistent x p

def hits (s : State) (node : JSString) : Nat → Option JSString → Bool
  | 0, _ => false
  | n + 1, cursor => match cursor with
    | none => false
    | some p => if p = node then true else hits s node n (s.parents.get p)

def after (s : State) (node : JSString) : Option JSString → State
  | none => s
  | some p => attached s node p

private def moveEnv (s : State) (node : JSString) (parent cursor old : Option JSString)
    (prior : Unit × State × Unit) :=
  (Loop.integers, (cursor, (s, (s, (old, ((), (prior, (JoinNative.«Tree#move#0», (node, (parent, ()))))))))))

private theorem move_body (s : State) (node : JSString) (parent cursor old : Option JSString)
    (prior : Unit × State × Unit) (i : Int) :
    JoinNative.«Tree#move#3» i (moveEnv s node parent cursor old prior) =
      match cursor with
      | none => .stop (moveEnv s node parent cursor old prior)
      | some p => if p = node then .ret ((), s, ())
        else .next (moveEnv s node parent (s.parents.get p) old prior) := by
  cases cursor with
  | none => simp [moveEnv]
  | some p => by_cases h : p = node <;> simp [moveEnv, h]

private theorem move_finish (s : State) (node : JSString) (parent cursor old : Option JSString)
    (prior : Unit × State × Unit) :
    JoinNative.«Tree#move#5» (moveEnv s node parent cursor old prior) = ((), after s node parent, ()) := by
  cases parent with
  | none => rfl
  | some p => cases h : s.children.get p <;> simp [moveEnv, after, attached, h]

private theorem move_loop (xs : List Int) (s : State) (node : JSString)
    (parent cursor old : Option JSString) (prior : Unit × State × Unit) :
    (Exit.elim (Loop.each xs (moveEnv s node parent cursor old prior) JoinNative.«Tree#move#3»)
      JoinNative.«Tree#move#5» id).2.1 =
      if hits s node xs.length cursor then s else after s node parent := by
  induction xs generalizing cursor with
  | nil => simp only [List.length_nil, Loop.each, Exit.elim, move_finish, hits, Bool.false_eq_true, ↓reduceIte]
  | cons i xs ih =>
    rw [Loop.each, move_body]
    cases cursor with
    | none => simp only [Exit.elim, move_finish, hits, List.length_cons, Bool.false_eq_true, ↓reduceIte]
    | some p =>
      by_cases h : p = node
      · simp [h, Exit.elim, hits]
      · simp only [h, ↓reduceIte, hits, List.length_cons]
        exact ih _

private theorem move_detach_parent (s : State) (node : JSString) (parent old : Option JSString)
    (prior : Unit × State × Unit) :
    (JoinNative.«Tree#move#6» (old, ((), (s, (s, (prior, (JoinNative.«Tree#move#0», (node, (parent, ()))))))))).2.1 =
      let detached := { s with parents := s.parents.delete node }
      if hits detached node detached.children.size parent then detached else after detached node parent := by
  change (Exit.elim (Loop.each (Loop.integers 0 (Int.ofNat s.children.size))
    (moveEnv { s with parents := s.parents.delete node } node parent parent old prior) JoinNative.«Tree#move#3»)
    JoinNative.«Tree#move#5» id).2.1 = _
  rw [move_loop]
  simp

private theorem move_detach (s : State) (node : JSString) (parent : Option JSString)
    (prior : Unit × State × Unit) :
    (JoinNative.«Tree#move#7» ((), (s, (s, (prior, (JoinNative.«Tree#move#0», (node, (parent, ())))))))).2.1 =
      let d := detached s node
      if hits d node d.children.size parent then d else after d node parent := by
  cases h : s.parents.get node with
  | none =>
    simpa only [JoinNative.«Tree#move#7», NativeDestruct.«Tree#state», h, Option.elim_none, detached]
      using move_detach_parent s node parent none prior
  | some old =>
    cases children : s.children.get old
    all_goals simpa only [JoinNative.«Tree#move#7», NativeDestruct.«Tree#state»,
      NativeConstruct.«Tree#state», h, children, Option.elim_some, Option.elim_none, Option.getD_some,
      Option.getD_none, detached, JSArray.filter_unindexed, bne]
      using (move_detach_parent { s with children := s.children.set old ((s.children.get old).getD [] |>.filter (· != node)) }
        node parent (some old) prior)

private theorem move_add (s : State) (node : JSString) :
    JoinNative.«Tree#move#2» (s, (node, ())) = ((), add s node, ()) := by
  simp only [JoinNative.«Tree#move#2», JoinNative.«Tree#move#1», NativeDestruct.«Tree#state»,
    NativeConstruct.«Tree#state», add]
  split <;> simp_all only [ite_true] <;> rfl

def move (s : State) (node : JSString) (parent : Option JSString) : State :=
  let a := add s node
  let a := parent.elim a (add a)
  let d := detached a node
  if hits d node d.children.size parent then d else after d node parent

theorem move_eq (s : State) (node : JSString) (parent : Option JSString) :
    («Tree#move» s node parent).2.1 = move s node parent := by
  cases parent with
  | none => simp only [«Tree#move», move_add, Option.elim_none, move_detach, move] <;> rfl
  | some p => simp only [«Tree#move», move_add, Option.elim_some, move_detach, move] <;> rfl

theorem move_consistent (s : State) (consistent : Consistent s) (node : JSString) (parent : Option JSString) :
    Consistent (move s node parent) := by
  let a := parent.elim (add s node) (add (add s node))
  have ca : Consistent a := by
    cases parent with
    | none => exact add_consistent s consistent node
    | some p => exact add_consistent _ (add_consistent s consistent node) p
  have cd := detached_consistent a ca node
  change Consistent (if hits (detached a node) node (detached a node).children.size parent then
    detached a node else after (detached a node) node parent)
  split
  · exact cd
  · cases parent with
    | none => exact cd
    | some p => exact attached_consistent _ cd node p (by simp [detached])

inductive Reachable : State → Prop where
  | fresh : Reachable «Tree##new»
  | add {s : State} (before : Reachable s) (node : JSString) : Reachable ((«Tree#add» s node).2.1)
  | move {s : State} (before : Reachable s) (node : JSString) (parent : Option JSString) :
      Reachable ((«Tree#move» s node parent).2.1)

theorem reachable_consistent {s : State} (reachable : Reachable s) : Consistent s := by
  induction reachable with
  | fresh => intro x p; simp [«Tree##new»]
  | add before node ih => rw [add_eq]; exact add_consistent _ ih node
  | move before node parent ih => rw [move_eq]; exact move_consistent _ ih node parent

theorem child_parent_agree {s : State} (reachable : Reachable s) (node parent : JSString) :
    node ∈ «Tree#childList» s parent ↔ «Tree#parent» s node = some parent := by
  rw [childList_eq, parent_eq]
  exact reachable_consistent reachable node parent

private theorem mem_keys_set (m : JSMap JSString α) (k q : JSString) (v : α)
    (known : q ∈ m.keys) : q ∈ (m.set k v).keys := by
  rw [JSMap.keys_set]
  split <;> simp_all

private theorem add_keys (s : State) (node q : JSString) (known : q ∈ s.children.keys) :
    q ∈ (add s node).children.keys := by
  unfold add
  split
  · exact known
  · exact mem_keys_set _ _ _ _ known

private theorem mem_keys_of_get (m : JSMap JSString α) (k : JSString) (v : α) (h : m.get k = some v) :
    k ∈ m.keys := by
  have : MapEntries.get m.entries k = some v := h
  change k ∈ m.entries.map Prod.fst
  generalize m.entries = entries at this ⊢
  induction entries with
  | nil => simp [MapEntries.get] at this
  | cons x xs ih =>
    rcases x with ⟨key, value⟩
    by_cases eq : key = k
    · simp [eq]
    · simp [MapEntries.get, eq] at this
      exact List.mem_cons_of_mem key (ih this)

private theorem add_known (s : State) (node : JSString) : node ∈ (add s node).children.keys := by
  unfold add
  split
  · rename_i present
    cases h : s.children.get node with
    | none => simp [JSMap.has, h] at present
    | some xs => exact mem_keys_of_get _ _ _ h
  · rw [JSMap.keys_set]; split
    · rename_i present
      cases h : s.children.get node with
      | none => simp [JSMap.has, h] at present
      | some xs => exact mem_keys_of_get _ _ _ h
    · simp

private theorem detached_keys (s : State) (node q : JSString) (known : q ∈ s.children.keys) :
    q ∈ (detached s node).children.keys := by
  cases h : s.parents.get node
  · simpa [detached, h] using known
  · simpa [detached, h] using mem_keys_set s.children _ q _ known

private theorem add_closed (s : State) (closed : Closed s) (node : JSString) : Closed (add s node) := by
  intro x p h
  have old : s.parents.get x = some p := by
    unfold add at h
    split at h <;> exact h
  exact ⟨add_keys s node x (closed x p old).1, add_keys s node p (closed x p old).2⟩

private theorem detached_closed (s : State) (closed : Closed s) (node : JSString) : Closed (detached s node) := by
  intro x p h
  have old : s.parents.get x = some p := by
    have hh : node ≠ x ∧ s.parents.get x = some p := by simpa [detached, JSMap.get_delete] using h
    exact hh.2
  exact ⟨detached_keys s node x (closed x p old).1, detached_keys s node p (closed x p old).2⟩

private theorem attached_closed (s : State) (closed : Closed s) (node parent : JSString)
    (hn : node ∈ s.children.keys) (hp : parent ∈ s.children.keys) : Closed (attached s node parent) := by
  intro x p h
  by_cases eq : node = x
  · subst x
    have : parent = p := by simpa [attached] using h
    subst p
    exact ⟨mem_keys_set _ _ _ _ hn, mem_keys_set _ _ _ _ hp⟩
  · have old : s.parents.get x = some p := by simpa [attached, JSMap.get_set, eq] using h
    exact ⟨mem_keys_set _ _ _ _ (closed x p old).1, mem_keys_set _ _ _ _ (closed x p old).2⟩

inductive Reaches (s : State) : JSString → JSString → Prop where
  | refl (node : JSString) : Reaches s node node
  | step {node parent target : JSString} (edge : s.parents.get node = some parent)
      (rest : Reaches s parent target) : Reaches s node target

private theorem chain_stable (s : State) (rank : JSString → Nat) (ranked : Ranked s rank)
    (n : Nat) (node : JSString) (enough : rank node < n) (m : Nat)
    (bound : (chain s n node).length ≤ m) : chain s m node = chain s n node := by
  induction n generalizing node m with
  | zero => omega
  | succ n ih =>
    cases m with
    | zero => simp [chain] at bound
    | succ m =>
      cases h : s.parents.get node with
      | none => simp [chain, h]
      | some p =>
        have := ranked node p h
        simp only [chain, h, List.length_cons] at bound ⊢
        rw [ih p (by omega) m (by omega)]

private theorem reaches_chain (s : State) (rank : JSString → Nat) (ranked : Ranked s rank)
    (n : Nat) (node target : JSString) (enough : rank node < n) (reach : Reaches s node target) :
    target ∈ chain s n node := by
  induction n generalizing node with
  | zero => omega
  | succ n ih =>
    cases reach with
    | refl => simp [chain]
    | step edge rest =>
      have := ranked _ _ edge
      simp only [chain, edge, List.mem_cons]
      exact Or.inr (ih _ (by omega) rest)

private theorem hits_none (s : State) (node : JSString) (n : Nat) : hits s node n none = false := by
  cases n <;> rfl

private theorem hits_chain (s : State) (node : JSString) (n : Nat) (cursor : JSString) :
    hits s node n (some cursor) = true ↔ node ∈ chain s n cursor := by
  induction n generalizing cursor with
  | zero => simp [hits, chain]
  | succ n ih =>
    by_cases eq : cursor = node
    · subst cursor; simp [hits, chain]
    · cases h : s.parents.get cursor <;> simp [hits, chain, h, eq, Ne.symm eq, hits_none, ih]

private theorem missed_unreachable (s : State) (rank : JSString → Nat) (ranked : Ranked s rank)
    (closed : Closed s) (node parent : JSString) (known : parent ∈ s.children.keys)
    (missed : hits s node s.children.size (some parent) = false) : ¬ Reaches s parent node := by
  intro reach
  have member := reaches_chain s rank ranked (rank parent + 1) parent node (by omega) reach
  have bound : (chain s (rank parent + 1) parent).length ≤ s.children.size := by
    have h := (chain_nodup s rank ranked (rank parent + 1) parent).length_le_of_subset
      (chain_subset s closed (rank parent + 1) parent known)
    simpa [JSMap.keys, JSMap.size] using h
  rw [← chain_stable s rank ranked (rank parent + 1) parent (by omega) s.children.size bound] at member
  have hit := (hits_chain s node s.children.size parent).mpr member
  simp [missed] at hit

private theorem reaches_edge (s : State) (x p target : JSString)
    (edge : s.parents.get x = some p) (different : x ≠ target) :
    Reaches s x target ↔ Reaches s p target := by
  constructor
  · intro reach
    cases reach with
    | refl => exact False.elim (different rfl)
    | step other rest =>
      have same := Option.some.inj (edge.symm.trans other)
      subst p
      exact rest
  · exact Reaches.step edge

private theorem add_ranked (s : State) (rank : JSString → Nat) (ranked : Ranked s rank) (node : JSString) :
    Ranked (add s node) rank := by
  unfold add
  split <;> exact ranked

private theorem detached_ranked (s : State) (rank : JSString → Nat) (ranked : Ranked s rank) (node : JSString) :
    Ranked (detached s node) rank := by
  intro x p edge
  have old : node ≠ x ∧ s.parents.get x = some p := by simpa [detached, JSMap.get_delete] using edge
  exact ranked x p old.2

private theorem attached_ranked (s : State) (rank : JSString → Nat) (ranked : Ranked s rank)
    (node parent : JSString) (unreachable : ¬ Reaches s parent node) :
    ∃ nextRank, Ranked (attached s node parent) nextRank := by
  classical
  refine ⟨fun x => if Reaches s x node then rank x + rank parent + 1 else rank x, ?_⟩
  intro x p edge
  by_cases same : node = x
  · subst x
    have same : parent = p := by simpa [attached] using edge
    subst p
    simp only [Reaches.refl, ↓reduceIte, unreachable]
    omega
  · have old : s.parents.get x = some p := by simpa [attached, JSMap.get_set, same] using edge
    have smaller := ranked x p old
    have equiv := reaches_edge s x p node old (Ne.symm same)
    by_cases affected : Reaches s x node
    · have hp := equiv.mp affected
      simp only [affected, hp, ↓reduceIte]
      omega
    · have hp : ¬ Reaches s p node := fun h => affected (equiv.mpr h)
      simp only [affected, hp, ↓reduceIte]
      exact smaller

def Forest (s : State) : Prop := Closed s ∧ ∃ rank, Ranked s rank

private theorem add_forest (s : State) (forest : Forest s) (node : JSString) : Forest (add s node) := by
  rcases forest with ⟨closed, rank, ranked⟩
  exact ⟨add_closed s closed node, rank, add_ranked s rank ranked node⟩

private theorem move_forest (s : State) (forest : Forest s) (node : JSString) (parent : Option JSString) :
    Forest (move s node parent) := by
  let a := parent.elim (add s node) (add (add s node))
  have fa : Forest a := by
    cases parent with
    | none => exact add_forest s forest node
    | some p => exact add_forest _ (add_forest s forest node) p
  have kn : node ∈ a.children.keys := by
    cases parent with
    | none => exact add_known s node
    | some p => exact add_keys _ p node (add_known s node)
  rcases fa with ⟨closed, rank, ranked⟩
  let d := detached a node
  have cd : Closed d := detached_closed a closed node
  have rd : Ranked d rank := detached_ranked a rank ranked node
  have nd : node ∈ d.children.keys := detached_keys a node node kn
  change Forest (if hits d node d.children.size parent then d else after d node parent)
  split
  · exact ⟨cd, rank, rd⟩
  · rename_i missed
    have missed : hits d node d.children.size parent = false := Bool.eq_false_iff.mpr missed
    cases parent with
    | none => exact ⟨cd, rank, rd⟩
    | some p =>
      have kp : p ∈ a.children.keys := add_known _ p
      have pd := detached_keys a node p kp
      exact ⟨attached_closed d cd node p nd pd,
        attached_ranked d rank rd node p (missed_unreachable d rank rd cd node p pd missed)⟩

theorem reachable_forest {s : State} (reachable : Reachable s) : Forest s := by
  induction reachable with
  | fresh =>
    constructor
    · intro x p h; simp [«Tree##new»] at h
    · refine ⟨fun _ => 0, ?_⟩
      intro x p h; simp [«Tree##new»] at h
  | add before node ih => rw [add_eq]; exact add_forest _ ih node
  | move before node parent ih => rw [move_eq]; exact move_forest _ ih node parent

theorem reachable_root {s : State} (reachable : Reachable s) (node : JSString) :
    «Tree#parent» s («Tree#root» s node) = none := by
  rcases reachable_forest reachable with ⟨closed, rank, ranked⟩
  exact root_reached s rank ranked closed node
end Examples.Proofs.ReferenceTree







