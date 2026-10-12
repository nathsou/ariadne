import Ariadne.Shallow.Denote

namespace Ariadne.Shallow
open Core
variable {interp : Named.Interp}

/-- Reconstruct the typed environment from its variable observations. -/
def Core.Env.ofLookup {interp : Named.Interp} :
    (Γ : List Core.Ty) → (∀ {t}, Var Γ t → t.denote interp) → Core.Env Γ interp
  | [], _ => ()
  | _ :: Γ, values => (values .here, ofLookup (interp := interp) Γ (fun v => values (.there v)))

@[simp] theorem Core.Var.get_ofLookup (v : Var Γ t) (values : ∀ {t}, Var Γ t → t.denote interp) :
    v.get (Core.Env.ofLookup (interp := interp) Γ values) = values v := by
  induction v with
  | here => rfl
  | there v ih => exact ih _

theorem Core.Env.ext_lookup {a b : Core.Env Γ interp}
    (equal : ∀ {t} (v : Var Γ t), v.get a = v.get b) : a = b := by
  induction Γ with
  | nil => cases a; cases b; rfl
  | cons t Γ ih =>
    apply Prod.ext
    · exact equal .here
    · apply ih
      intro t v
      exact equal (.there v)

def Core.Renaming.pull (r : Renaming Γ Δ) (env : Core.Env Δ interp) : Core.Env Γ interp :=
  Core.Env.ofLookup (interp := interp) Γ (fun v => (r v).get env)

@[simp] theorem Core.Renaming.pull_lift {a : Core.Ty} (r : Renaming Γ Δ) (env : Core.Env Δ interp) (x : a.denote interp) :
    Core.Renaming.pull (Core.Renaming.lift r) (x, env) = (x, r.pull env) := by
  apply Core.Env.ext_lookup
  intro t v
  cases v with
  | here => rfl
  | there v => simp [Core.Renaming.pull, Core.Renaming.lift, Core.Var.get, Core.Env.ofLookup]

/-- Renaming only changes the environment through which variables are read. -/
theorem Denote.rename (term : Term Γ t) (r : Renaming Γ Δ) (env : Core.Env Δ interp) :
    Denote.term (interp := interp) (term.rename r) env = Denote.term (interp := interp) term (r.pull env) := by
  induction term generalizing Δ with
  | var v => simp [Term.rename, Denote.term, Core.Renaming.pull]
  | let_ name a b ha hb =>
    simp only [Term.rename, Denote.term, hb, ha, Core.Renaming.pull_lift]
  | lam name body ih =>
    funext x
    simp only [Term.rename, Denote.term, ih, Core.Renaming.pull_lift]
  | optionCase a b c ha hb hc =>
    simp only [Term.rename, Denote.term, ha, hb, hc, Core.Renaming.pull_lift]
  | sumCase a b c ha hb hc =>
    simp only [Term.rename, Denote.term, ha, hb, hc, Core.Renaming.pull_lift]
  | _ => simp_all only [Term.rename, Denote.term]

def Core.Substitution.eval (s : Substitution Γ Δ) (env : Core.Env Δ interp) : Core.Env Γ interp :=
  Core.Env.ofLookup (interp := interp) Γ (fun v => Denote.term (interp := interp) (s v) env)

@[simp] theorem Core.Substitution.eval_lift {a : Core.Ty} (s : Substitution Γ Δ) (env : Core.Env Δ interp) (x : a.denote interp) :
    Core.Substitution.eval (Core.Substitution.lift s) (x, env) = (x, s.eval env) := by
  apply Core.Env.ext_lookup
  intro t v
  cases v with
  | here => rfl
  | there v =>
    simp [Core.Substitution.eval, Core.Substitution.lift, Core.Var.get, Core.Env.ofLookup, Denote.rename]
    congr 1
    apply Core.Env.ext_lookup
    intro t w
    simp [Core.Renaming.pull, Core.Var.get]

/-- Typed substitution commutes with the native interpretation. -/
theorem Denote.substitute (term : Term Γ t) (s : Substitution Γ Δ) (env : Core.Env Δ interp) :
    Denote.term (interp := interp) (term.substitute s) env = Denote.term (interp := interp) term (s.eval env) := by
  induction term generalizing Δ with
  | var v => simp [Term.substitute, Denote.term, Core.Substitution.eval]
  | let_ name a b ha hb =>
    simp only [Term.substitute, Denote.term, hb, ha, Core.Substitution.eval_lift]
  | lam name body ih =>
    funext x
    simp only [Term.substitute, Denote.term, ih, Core.Substitution.eval_lift]
  | optionCase a b c ha hb hc =>
    simp only [Term.substitute, Denote.term, ha, hb, hc, Core.Substitution.eval_lift]
  | sumCase a b c ha hb hc =>
    simp only [Term.substitute, Denote.term, ha, hb, hc, Core.Substitution.eval_lift]
  | _ => simp_all only [Term.substitute, Denote.term]

end Ariadne.Shallow
