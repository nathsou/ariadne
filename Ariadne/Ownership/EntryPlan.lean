import Ariadne.Shallow.ClassPlan

namespace Ariadne.Ownership

inductive Traversal where
  | root
  | deep
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

structure ArgumentCheck where
  left : Nat
  right : Nat
  leftTraversal : Traversal
  rightTraversal : Traversal
  projection : Option Projection.Kind := none
  deriving Repr, BEq

/-- Readonly views and compatible structural views can denote the same object.
Union alternatives describe a root, rather than an additional containment edge. -/
def rootMatches : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    match Check.unreadonly a, Check.unreadonly b with
    | .union x y, b => rootMatches fuel x b || rootMatches fuel y b
    | a, .union x y => rootMatches fuel a x || rootMatches fuel a y
    | a, b => Check.referenceType a && Check.referenceType b &&
        (a == b || Check.compatible a b || Check.compatible b a)

/-- Only public class fields expose containment to another exported argument.
Private field references cannot escape the checked class discipline. -/
def exposedChildren (program : Program) (ty : Ty) : Checked (List Ty) := do
  match Check.unreadonly ty with
  | .array element => return [element]
  | .map _ value => return [value]
  | .record fields => return fields.map (Check.unreadonly ·.2)
  | .tuple elements => return elements
  | .class_ name =>
    let some class_ := program.classes.find? (·.name == name)
      | Check.error "A2001" s!"unknown class '{name}'" {}
    (class_.fields.filter (!·.private_)).mapM fun field => do
      match field.ty with
      | some ty => Check.resolve 100 program ty
      | none => Check.infer 256 {program} field.value
  | _ => return []

/-- A cycle in the class type graph is visited once. Exhaustion refuses the
plan instead of silently selecting an incomplete shallow check. -/
def occurs (program : Program) (needle : Ty) : Nat → List String → Ty → Checked Bool
  | 0, _, _ => Check.error "A5101" "entry guard type-containment budget exhausted" {}
  | fuel + 1, visited, candidate => do
    let candidate ← Check.resolve 100 program candidate
    if rootMatches 100 needle candidate then return true
    match Check.unreadonly candidate with
    | .union a b => return (← occurs program needle fuel visited a) ||
        (← occurs program needle fuel visited b)
    | .class_ name =>
      if visited.contains name then return false
      for child in ← exposedChildren program candidate do
        if ← occurs program needle fuel (name :: visited) child then return true
      return false
    | _ =>
      for child in ← exposedChildren program candidate do
        if ← occurs program needle fuel visited child then return true
      return false

def nested (program : Program) (needle : Ty) : Nat → Ty → Checked Bool
  | 0, _ => Check.error "A5101" "entry guard type-containment budget exhausted" {}
  | fuel + 1, container => do
    let container ← Check.resolve 100 program container
    match Check.unreadonly container with
    | .union a b => return (← nested program needle fuel a) || (← nested program needle fuel b)
    | _ =>
      for child in ← exposedChildren program container do
        if ← occurs program needle fuel [] child then return true
      return false

/-- Every pair with a mutated argument is checked. Deep traversal is selected
only for a possible containment path, in either direction. Unrelated immutable
arguments need no guard. -/
def entryPlan (program : Program) (function : Ariadne.Function) : Checked (List ArgumentCheck) := do
  let types ← function.params.mapM fun param => Check.resolve 100 program param.ty
  let mut plan := []
  if let some entry := Projection.simultaneousEntry function then
    let left := function.params.findIdx (·.name == entry.leftKey)
    let right := function.params.findIdx (·.name == entry.rightKey)
    plan := [{left, right, leftTraversal := .root, rightTraversal := .root, projection := some entry.left.kind}]
  if (types.filter Check.referenceType).length < 2 || types.all Check.immutable then return plan
  let lowered ← Shallow.ClassPlan.lower program
  let writes ← Shallow.StatePlan.effects lowered 256 function
  for left in List.range types.length do
    for right in List.range types.length do
      if left < right then
        let a := types[left]!
        let b := types[right]!
        if Check.referenceType a && Check.referenceType b &&
            (writes.contains function.params[left]!.name || writes.contains function.params[right]!.name) then
          let leftTraversal : Traversal := if ← nested program b 512 a then .deep else .root
          let rightTraversal : Traversal := if ← nested program a 512 b then .deep else .root
          plan := plan ++ [{left := left, right := right, leftTraversal, rightTraversal}]
  return plan

end Ariadne.Ownership
