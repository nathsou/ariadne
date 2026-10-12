import Ariadne.Ownership.Forest
import Ariadne.Ownership.Guard
import Ariadne.Shallow.Adequacy.Array

namespace Ariadne.Ownership
open Heap

/-- An actual path through the public heap layout inspected by the generated
guard. Class-private edges do not appear in this relation. -/
inductive PublicPath (program : Program) (heap : Heap) : Nat → List Nat → Nat → Prop where
  | self (address : Nat) : PublicPath program heap address [address] address
  | child {address next target : Nat} {nodes : List Nat} {object : Object} {values : List Value}
      (lookup : heap[address]? = some object)
      (children : publicChildren program object = .ok values)
      (member : .ref next ∈ values) (tail : PublicPath program heap next nodes target) :
      PublicPath program heap address (address :: nodes) target

/-- Even an invalid earlier sibling makes the guard fail, rather than letting
an overlap pass. Only an `ok false` search result needs to be excluded. -/
theorem PublicPath.not_false {program : Program} {heap : Heap} {address target : Nat}
    {nodes : List Nat} (path : PublicPath program heap address nodes target)
    (simple : nodes.Nodup) (fuel : Nat) (visited : List Nat)
    (outside : ∀ node ∈ nodes, node ∉ visited) :
    containsReference program heap target fuel visited (.ref address) ≠ .ok false := by
  induction path generalizing fuel visited with
  | self address => cases fuel <;> simp [containsReference, pure, Except.pure]
  | @child address next target nodes object values lookup children member tail ih =>
    intro failed
    have fresh : address ∉ visited := outside address (by simp)
    by_cases same : address = target
    · subst address
      cases fuel <;> simp [containsReference, pure, Except.pure] at failed
    · cases fuel with
      | zero => simp [containsReference, same, fresh] at failed
      | succ fuel =>
        have searched : anyResult (containsReference program heap target fuel (address :: visited)) values = .ok false := by
          simpa [containsReference, same, fresh, lookup, children, bind, Except.bind] using failed
        have nextFailed := anyResult_false_iff.mp searched (.ref next) member
        have parts := List.nodup_cons.mp simple
        apply ih parts.2 fuel (address :: visited) _ nextFailed
        intro node inside seen
        rcases List.mem_cons.mp seen with equal | old
        · subst node; exact parts.1 inside
        · exact outside node (by simp [inside]) old

/-- Structural entry facts are about the ownership tree, types and visibility,
not separation of the input footprints. A root-only plan requires absence of
a proper typed containment path. Private descendants cannot themselves be
exported argument roots; public ancestry has an actual heap path. -/
structure EntryShape (program : Program) (heap : Heap) (parents : Parents)
    (check : ArgumentCheck) (left right : Nat) (a b : Footprint) : Prop where
  leftRooted : Rooted parents left a
  rightRooted : Rooted parents right b
  leftNonnested : check.leftTraversal = .root → Ancestor parents right left → right = left
  rightNonnested : check.rightTraversal = .root → Ancestor parents left right → left = right
  leftPublic : Ancestor parents right left → ∃ nodes, PublicPath program heap left nodes right ∧ nodes.Nodup
  rightPublic : Ancestor parents left right → ∃ nodes, PublicPath program heap right nodes left ∧ nodes.Nodup

/-- Scalar containers have singleton read/write footprints. This constructs
their entry facts directly, even when their surrounding host heap has owners. -/
theorem EntryShape.flat (program : Program) (heap : Heap) (check : ArgumentCheck) (left right : Nat) :
    EntryShape program heap (fun _ => none) check left right [left] [right] := by
  constructor
  ·
    intro address member
    have same : address = left := by simpa using member
    subst address
    exact .self left
  ·
    intro address member
    have same : address = right := by simpa using member
    subst address
    exact .self right
  · exact fun _ path => path.equal_of_no_parent rfl
  · exact fun _ path => path.equal_of_no_parent rfl
  ·
    intro path
    have same := path.equal_of_no_parent rfl
    subst right
    exact ⟨[left], .self left, by simp⟩
  ·
    intro path
    have same := path.equal_of_no_parent rfl
    subst left
    exact ⟨[right], .self right, by simp⟩

/-- One guard theorem supplies footprint separation to every stateful transfer
rule. No input-disjointness premise is used. The remaining checker adequacy
obligation establishes `EntryShape` from the typed ownership invariant. -/
theorem checkArgument_disjoint {program : Program} {heap : Heap} {parents : Parents}
    {args : List Value} {check : ArgumentCheck} {left right : Nat} {a b : Footprint}
    (shape : EntryShape program heap parents check left right a b)
    (leftArg : args[check.left]? = some (.ref left))
    (rightArg : args[check.right]? = some (.ref right))
    (passed : checkArgument program heap args check = .ok ()) : Disjoint a b := by
  obtain ⟨different, leftPassed, rightPassed⟩ := (checkArgument_iff leftArg rightArg).mp passed
  apply rooted_disjoint shape.leftRooted shape.rightRooted
  · intro path
    cases walk : check.rightTraversal with
    | root => exact different (shape.rightNonnested walk path)
    | deep =>
      obtain ⟨nodes, pathSeen, simple⟩ := shape.rightPublic path
      exact pathSeen.not_false simple heap.length [] (by simp) (rightPassed walk)
  · intro path
    cases walk : check.leftTraversal with
    | root => exact different (shape.leftNonnested walk path).symm
    | deep =>
      obtain ⟨nodes, pathSeen, simple⟩ := shape.leftPublic path
      exact pathSeen.not_false simple heap.length [] (by simp) (leftPassed walk)

private theorem scalar_elements_footprint {relation : Value → α → Prop}
    {heap : Heap} {values : List Value} {natives : List α} {footprint : Footprint}
    (related : Shallow.DataRelation.Elements (Shallow.DataRelation.scalar relation)
      heap values natives footprint) : footprint = [] := by
  induction related with
  | nil => rfl
  | cons head _ _ ih =>
    have empty := head.2
    simp only [empty, ih, List.nil_append]

theorem scalar_array_footprint {relation : Value → α → Prop} {heap : Heap}
    {address : Nat} {values : List α} {footprint : Footprint}
    (related : (Shallow.DataRelation.scalar relation).array.Holds heap (.ref address) values footprint) :
    footprint = [address] := by
  obtain ⟨root, runtime, children, same, _, contents, _, footprintEq⟩ :=
    Shallow.Adequacy.array_contents related
  have equal : address = root := Value.ref.inj same
  subst root
  simpa only [scalar_elements_footprint contents] using footprintEq

/-- A passing generated guard separates actual scalar-array layouts, using
their heap representation premises rather than an input-disjointness premise. -/
theorem scalar_arrays_guard_disjoint {program : Program} {heap : Heap} {args : List Value}
    {check : ArgumentCheck} {left right : Nat} {a b : Footprint}
    {leftRelation : Value → α → Prop} {rightRelation : Value → β → Prop}
    {leftValues : List α} {rightValues : List β}
    (leftLayout : (Shallow.DataRelation.scalar leftRelation).array.Holds heap (.ref left) leftValues a)
    (rightLayout : (Shallow.DataRelation.scalar rightRelation).array.Holds heap (.ref right) rightValues b)
    (leftArg : args[check.left]? = some (.ref left)) (rightArg : args[check.right]? = some (.ref right))
    (passed : checkArgument program heap args check = .ok ()) : Disjoint a b := by
  rw [scalar_array_footprint leftLayout, scalar_array_footprint rightLayout]
  exact checkArgument_disjoint (EntryShape.flat program heap check left right) leftArg rightArg passed

end Ariadne.Ownership
