import Ariadne.Shallow.Declarations

namespace Ariadne.Shallow.Declarations

def branchName (name : String) (left : Bool) : String := name ++ if left then "#left" else "#right"

def variantAliases : Nat → String → Ariadne.Ty → List (String × Ariadne.Ty)
  | 0, _, _ => []
  | n + 1, name, .union a b =>
    if a == .undefined || b == .undefined then [] else
      let left := branchName name true
      let right := branchName name false
      [(left, a), (right, b)] ++ variantAliases n left a ++ variantAliases n right b
  | n + 1, name, .readonly ty | n + 1, name, .fieldReadonly ty => variantAliases n name ty
  | _, _, _ => []

def withVariants (p : Program) : Checked Program := do
  let mut aliases := p.aliases
  for (name, source) in p.aliases do
    let resolved ← Check.resolve 100 p source
    aliases := aliases ++ variantAliases 100 name resolved
  return { p with aliases }

def union (p : Program) (declaration : Named.Declaration) (span : Span) :
    Checked (Option (Info × Info)) := do
  let actual ← info p declaration.name span
  if actual.declaration != declaration then unsupported "named declaration shape mismatch" span
  match Check.unreadonly actual.source with
  | .union a b =>
    if a == .undefined || b == .undefined then return none
    return some (← info p (branchName declaration.name true) span,
      ← info p (branchName declaration.name false) span)
  | _ => return none

/-- A narrowed view may be injected only into the matching parent declaration.
Both its generated path and its complete canonical shape are checked. -/
def inject : (parent child : Named.Declaration) → Core.Term Γ (Core.shapeType child.shape) →
    Option (Core.Term Γ (Core.shapeType parent.shape))
  | parent, child, value => go 100 parent.name parent.shape child value
where
  go : Nat → String → (shape : Named.Shape) → (child : Named.Declaration) →
      Core.Term Γ (Core.shapeType child.shape) → Option (Core.Term Γ (Core.shapeType shape))
    | 0, _, _, _, _ => none
    | n + 1, name, shape, child, value =>
      let exact : Option (Core.Term Γ (Core.shapeType shape)) :=
        if equal : shape = child.shape then
          if name == child.name then some (equal.symm ▸ value) else none
        else none
      match exact with
      | some value => some value
      | none =>
        match shape with
        | .sum a b =>
          match go n (branchName name true) a child value with
          | some left => some (.inl left)
          | none => (go n (branchName name false) b child value).map Core.Term.inr
        | _ => none

end Ariadne.Shallow.Declarations
