import Ariadne.Heap

namespace Ariadne.Ownership
open Heap

/-- The parent relation concerns owned mutable objects. Shared immutable
objects have no owning edge and are accounted for as read observations. -/
abbrev Parents := Nat → Option Nat

inductive Ancestor (parents : Parents) : Nat → Nat → Prop where
  | self (address : Nat) : Ancestor parents address address
  | parent {address above root : Nat} : parents address = some above →
      Ancestor parents above root → Ancestor parents address root

theorem Ancestor.equal_of_no_parent {parents : Parents} {address root : Nat}
    (path : Ancestor parents address root) (none : parents address = .none) : address = root := by
  cases path with
  | self => rfl
  | parent found _ => rw [none] at found; cases found

/-- A unique owning parent makes the ancestors of any object a chain. This
is the reason two roots cannot secretly share an owned mutable descendant. -/
theorem Ancestor.comparable {parents : Parents} {address left right : Nat}
    (a : Ancestor parents address left) (b : Ancestor parents address right) :
    Ancestor parents left right ∨ Ancestor parents right left := by
  induction a with
  | self => exact Or.inl b
  | @parent address above left parent path ih =>
    cases b with
    | self => exact Or.inr (.parent parent path)
    | @parent _ other _ found tail =>
      have same : above = other := Option.some.inj (parent.symm.trans found)
      subst other
      exact ih tail

def Rooted (parents : Parents) (root : Nat) (footprint : Footprint) : Prop :=
  ∀ address ∈ footprint, Ancestor parents address root

theorem rooted_disjoint {parents : Parents} {left right : Nat} {a b : Footprint}
    (leftRooted : Rooted parents left a) (rightRooted : Rooted parents right b)
    (leftOutside : ¬Ancestor parents left right)
    (rightOutside : ¬Ancestor parents right left) : Disjoint a b := by
  intro address ha hb
  rcases (leftRooted address ha).comparable (rightRooted address hb) with path | path
  · exact leftOutside path
  · exact rightOutside path

/-- A finite operational ancestry query. The rank invariant below gives a
complete bound and excludes owned cycles without depending on evaluator fuel. -/
def ancestorCheck (parents : Parents) : Nat → Nat → Nat → Bool
  | 0, address, root => address == root
  | fuel + 1, address, root =>
    if address == root then true else
      match parents address with
      | none => false
      | some above => ancestorCheck parents fuel above root

theorem ancestorCheck_sound {parents : Parents} {fuel address root : Nat}
    (passed : ancestorCheck parents fuel address root = true) : Ancestor parents address root := by
  induction fuel generalizing address with
  | zero =>
    have same : address = root := by simpa [ancestorCheck] using passed
    subst address
    exact .self root
  | succ fuel ih =>
    by_cases same : address = root
    · subst address; exact .self root
    · cases found : parents address with
      | none => simp [ancestorCheck, same, found] at passed
      | some above =>
        exact .parent found (ih (by simpa [ancestorCheck, same, found] using passed))

structure Ranked (parents : Parents) where
  rank : Nat → Nat
  decreases : ∀ {address above}, parents address = some above → rank above < rank address

theorem ancestorCheck_complete {parents : Parents} (tree : Ranked parents)
    {fuel address root : Nat} (bound : tree.rank address < fuel)
    (path : Ancestor parents address root) : ancestorCheck parents fuel address root = true := by
  induction fuel generalizing address with
  | zero => omega
  | succ fuel ih =>
    by_cases same : address = root
    · simp [ancestorCheck, same]
    · cases path with
      | self => exact False.elim (same rfl)
      | @parent _ above _ found tail =>
        have smaller := tree.decreases found
        have remaining : tree.rank above < fuel := by omega
        simpa [ancestorCheck, same, found] using ih remaining tail

end Ariadne.Ownership
