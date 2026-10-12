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

/-- Named data has a closed canonical shape. Literal fields carry no data; their
known source value is restored when the field is observed. -/
def shape (span : Span) : Nat → Ariadne.Ty → Checked Named.Shape
  | 0, _ => unsupported "named data exceeds the type nesting budget" span
  | _ + 1, .void | _ + 1, .undefined | _ + 1, .stringLiteral _ => .ok .unit
  | _ + 1, .boolean => .ok .bool
  | _ + 1, .int53 => .ok .int53
  | _ + 1, .bigint => .ok .int
  | _ + 1, .number => .ok .number
  | _ + 1, .string => .ok .string
  | n + 1, .readonly ty | n + 1, .fieldReadonly ty => shape span n ty
  | n + 1, .array ty => return .list (← shape span n ty)
  | n + 1, .map k v => return .map (← key k span) (← shape span n v)
  | _ + 1, .set k => return .set (← key k span)
  | n + 1, .union ty .undefined | n + 1, .union .undefined ty => return .option (← shape span n ty)
  | n + 1, .union a b => return .sum (← shape span n a) (← shape span n b)
  | n + 1, .tuple [a, b] => return .pair (← shape span n a) (← shape span n b)
  | n + 1, .record fields => fields.foldrM (fun (_, ty) rest => do return .pair (← shape span n ty) rest) .unit
  | _, _ => unsupported "this named field has no canonical data representation" span

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
