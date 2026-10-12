import Ariadne.Target
import Ariadne.Fuel
import Ariadne.Check

namespace Ariadne.Compile

/-- Proof-carrying compilation. Rendering is untrusted and is checked separately
against `code`; the preservation proof is part of every successful result. -/
structure Fragment (α : Type) (meaning : α) where
  code : α
  correct : code = meaning
  text : String

abbrev Expression (p : Program) (e : Expr) :=
  Fragment Target.Expression (fun fuel s => evalExpr p fuel s e)
abbrev Command (p : Program) (s : Stmt) :=
  Fragment Target.Command (fun fuel state => exec p fuel state s)
abbrev Block (p : Program) (ss : List Stmt) :=
  Fragment Target.Command (fun fuel state => execBlock p fuel state ss)

def app (name : String) (args : List String) : String :=
  "(Target." ++ name ++ String.join (args.map (" " ++ ·)) ++ ")"

/-- Indent nested target commands; expressions remain compact. -/
def commandApp (name : String) (args : List String) : String :=
  "(Target." ++ name ++ String.join (args.map fun arg =>
    "\n  " ++ arg.replace "\n" "\n  ") ++ ")"

def unsupported (span : Span) (what : String) : Diagnostic :=
  { code := "A4101", span, message := s!"Scalar compilation does not yet support {what}",
    help := some "Use translate/certify for the operational model, or extract a function in the scalar compiler subset." }

def exhausted (span : Span) : Diagnostic :=
  { code := "A4102", span, message := "Scalar compiler nesting budget exhausted",
    help := some "Split deeply nested expressions or blocks into smaller pieces." }

theorem loop_correct (p : Program) (guard : Expr) (body : Stmt) (update : Option Stmt) :
    Target.loop (fun n s => evalExpr p n s guard) (fun n s => exec p n s body)
      (update.map fun stmt n s => exec p n s stmt) =
    (fun n s => Ariadne.loop p n s guard body update) := by
  funext n s
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [Target.loop, Ariadne.loop]
    cases update <;> simp only [Option.map] at ih ⊢ <;> simp only [ih]

end Ariadne.Compile
