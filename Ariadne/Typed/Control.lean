/-! Continuations shared by the canonical and named interpretations.
Only the environment type varies; mapping and exit behavior are identical. -/
namespace Ariadne

structure Control (Environment Result : Type) where
  normal : Environment → Result
  brk : Environment → Result
  cont : Environment → Result

abbrev Control.map (f : Environment' → Environment) (k : Control Environment Result) : Control Environment' Result :=
  ⟨k.normal ∘ f, k.brk ∘ f, k.cont ∘ f⟩

abbrev Control.all (r : Environment → Result) : Control Environment Result := ⟨r, r, r⟩

abbrev Control.post (k : Control Environment A) (h : A → B) : Control Environment B :=
  ⟨h ∘ k.normal, h ∘ k.brk, h ∘ k.cont⟩

end Ariadne
