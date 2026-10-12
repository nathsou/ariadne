import Ariadne.Check
import Ariadne.Shallow.Core

namespace Ariadne.Shallow.Declarations

def unsupported (message : String) (span : Span) : Checked α :=
  .error { code := "A5102", message, span }

def key (ty : Ariadne.Ty) (span : Span) : Checked Core.Key :=
  match Check.unreadonly ty with
  | .int53 => .ok .int53
  | .bigint => .ok .int
  | .number => .ok .number
  | .string | .stringLiteral _ => .ok .string
  | .boolean => .ok .bool
  | _ => unsupported "named data requires scalar collection keys" span

def fixedString (ty : Ariadne.Ty) : Option JSString :=
  match Check.unreadonly ty with
  | .stringLiteral value => some value
  | _ => none

def undefinedOnly : Ariadne.Ty → Bool
  | .void | .undefined => true
  | .readonly t | .fieldReadonly t => undefinedOnly t
  | .union a b => undefinedOnly a && undefinedOnly b
  | _ => false

def optionalShape : Named.Shape → Named.Shape
  | .option t => .option t
  | t => .option t

/-- Only direct fixed record fields erase their known string literal. Collection
and optional payloads retain strings so their unit cannot mean undefined. -/
def shape (span : Span) (fuel : Nat) (ty : Ariadne.Ty) : Checked Named.Shape :=
  convert fuel true ty
where
  convert : Nat → Bool → Ariadne.Ty → Checked Named.Shape
    | 0, _, _ => unsupported "named data exceeds the type nesting budget" span
    | _ + 1, _, .void | _ + 1, _, .undefined => .ok .unit
    | _ + 1, field, .stringLiteral _ => .ok (if field then .unit else .string)
    | _ + 1, _, .boolean => .ok .bool
    | _ + 1, _, .int53 => .ok .int53
    | _ + 1, _, .bigint => .ok .int
    | _ + 1, _, .number => .ok .number
    | _ + 1, _, .string => .ok .string
    | n + 1, field, .readonly ty | n + 1, field, .fieldReadonly ty => convert n field ty
    | n + 1, _, .array ty => return .list (← convert n false ty)
    | n + 1, _, .map k v => return .map (← key k span) (← convert n false v)
    | _ + 1, _, .set k => return .set (← key k span)
    | n + 1, _, .union ty .undefined | n + 1, _, .union .undefined ty => do
      if undefinedOnly ty then return .unit
      return optionalShape (← convert n false ty)
    | n + 1, _, .union a b => return .sum (← convert n false a) (← convert n false b)
    | n + 1, _, .tuple [a, b] => return .pair (← convert n false a) (← convert n false b)
    | n + 1, _, .record fields => fields.foldrM (fun (_, ty) rest => do return .pair (← convert n true ty) rest) .unit
    | _, _, _ => unsupported "this named field has no canonical data representation" span

structure Info where
  declaration : Named.Declaration
  source : Ariadne.Ty

def info (p : Program) (name : String) (span : Span) : Checked Info := do
  let some source := p.aliases.lookup name | unsupported "unknown named data declaration" span
  let source ← Check.resolve 100 p source
  return { declaration := ⟨name, ← shape span 100 source⟩, source }

def record (p : Program) (declaration : Named.Declaration) (span : Span) : Checked (List (String × Ariadne.Ty)) := do
  let actual ← info p declaration.name span
  if actual.declaration != declaration then unsupported "named declaration shape mismatch" span
  let .record fields := Check.unreadonly actual.source
    | unsupported "this named declaration requires union elimination" span
  if (fields.map Prod.fst).eraseDups.length != fields.length then
    unsupported "named records require unique field declarations" span
  return fields

end Ariadne.Shallow.Declarations
