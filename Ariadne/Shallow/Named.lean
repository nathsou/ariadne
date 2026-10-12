import Ariadne.Shallow.Key

namespace Ariadne.Shallow.Named

/-- Canonical data carried by a named declaration. Nested source declarations
are expanded here; native declarations can retain their original field types. -/
inductive Shape where
  | unit | bool | int | int53 | number | string
  | option (value : Shape)
  | list (element : Shape)
  | map (key : Core.Key) (value : Shape)
  | set (key : Core.Key)
  | pair (left right : Shape)
  | sum (left right : Shape)
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev Shape.denote : Shape → Type
  | .unit => Unit
  | .bool => Bool
  | .int | .int53 => Int
  | .number => Float.Model
  | .string => JSString
  | .option value => Option value.denote
  | .list element => List element.denote
  | .map key value => key.Map value.denote
  | .set key => key.Set
  | .pair left right => left.denote × right.denote
  | .sum left right => Sum left.denote right.denote

structure Declaration where
  name : String
  shape : Shape
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Every named representation carries its constructor/destructor laws. The
denotation may use any such representation, including emitted Lean structures
and tagged inductive types. -/
structure Representation (shape : Shape) where
  Native : Type
  construct : shape.denote → Native
  destruct : Native → shape.denote
  destruct_construct : ∀ value, destruct (construct value) = value
  construct_destruct : ∀ value, construct (destruct value) = value

abbrev Interp := (declaration : Declaration) → Representation declaration.shape

def Representation.canonical (shape : Shape) : Representation shape :=
  { Native := shape.denote, construct := id, destruct := id,
    destruct_construct := fun _ => rfl, construct_destruct := fun _ => rfl }

def canonical : Interp := fun declaration => Representation.canonical declaration.shape

def Lawful (interp : Interp) : Prop :=
  ∀ declaration, (∀ value, (interp declaration).destruct ((interp declaration).construct value) = value) ∧
    (∀ value, (interp declaration).construct ((interp declaration).destruct value) = value)

theorem lawful (interp : Interp) : Lawful interp := fun declaration =>
  ⟨(interp declaration).destruct_construct, (interp declaration).construct_destruct⟩

theorem Representation.construct_injective (repr : Representation shape) : Function.Injective repr.construct := by
  intro a b equal
  have := congrArg repr.destruct equal
  simpa only [repr.destruct_construct] using this

theorem Representation.destruct_injective (repr : Representation shape) : Function.Injective repr.destruct := by
  intro a b equal
  have := congrArg repr.construct equal
  simpa only [repr.construct_destruct] using this

def Representation.transport {a b : Shape} (equal : a = b) (repr : Representation a) : Representation b :=
  equal ▸ repr

/-- Install a native declaration, retaining the existing interpretation elsewhere.
The equality is on the name and shape together, so incompatible declarations
cannot silently reuse a native representation. -/
def Interp.insert (base : Interp) (declaration : Declaration) (repr : Representation declaration.shape) : Interp :=
  fun query => if h : query = declaration then Representation.transport (congrArg Declaration.shape h.symm) repr
    else base query

@[simp] theorem Interp.insert_self (base : Interp) (declaration : Declaration)
    (repr : Representation declaration.shape) : base.insert declaration repr declaration = repr := by
  simp [insert, Representation.transport]

theorem Interp.insert_other (base : Interp) (declaration query : Declaration)
    (repr : Representation declaration.shape) (distinct : query ≠ declaration) :
    base.insert declaration repr query = base query := by simp [insert, distinct]

end Ariadne.Shallow.Named
