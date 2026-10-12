import Ariadne.Shallow.Safety
namespace Ariadne.Shallow.Safety
open Core
/- Structural environment operations retain guarded function values. -/
namespace Environment
 def ofLookup {interp : Named.Interp} : (Γ : List Core.Ty) → (∀ {t}, Var Γ t → Model t interp) → Environment Γ interp
  | [], _ => ()
  | _ :: Γ, lookup => (lookup .here, ofLookup Γ (fun v => lookup (.there v)))
 theorem get_ofLookup {interp : Named.Interp} (lookup : ∀ {t}, Var Γ t → Model t interp) (v : Var Γ t) :
   getVariable v (ofLookup Γ lookup) = lookup v := by
   induction v <;> simp_all [ofLookup, getVariable]
 theorem ext {interp : Named.Interp} {a b : Environment Γ interp}
    (same : ∀ {t} (v : Var Γ t), getVariable v a = getVariable v b) : a = b := by
   induction Γ with
   | nil => cases a; cases b; rfl
   | cons t Γ ih =>
     apply Prod.ext
     · exact same .here
     · apply ih; intro t v; exact same (.there v)
 def pull {interp : Named.Interp} (r : Renaming Γ Δ) (env : Environment Δ interp) : Environment Γ interp :=
   ofLookup Γ (fun v => getVariable (r v) env)
 theorem get_pull {interp : Named.Interp} (r : Renaming Γ Δ) (env : Environment Δ interp) (v : Var Γ t) :
   getVariable v (pull r env) = getVariable (r v) env := get_ofLookup _ v
 theorem pull_lift {interp : Named.Interp} (r : Renaming Γ Δ) (env : Environment Δ interp) (value : Model a interp) :
   pull r.lift (value, env) = (value, pull r env) := by
   apply ext; intro t v
   rw [get_pull]
   cases v with
   | here => rfl
   | there v => simpa [Renaming.lift, getVariable] using (get_pull r env v).symm
 theorem pull_there {interp : Named.Interp} (env : Environment Γ interp) (value : Model a interp) :
   pull (Δ := a :: Γ) (fun v => .there v) (value, env) = env := by
   apply ext; intro t v; rw [get_pull]; rfl
end Environment
/-- Renaming preserves both the value and every collected guard. -/
 theorem term_rename {interp : Named.Interp} (body : Term Γ t) (r : Renaming Γ Δ) (env : Environment Δ interp) :
   term (body.rename r) env = term body (Environment.pull r env) := by
   induction body generalizing Δ with
   | var v => simp [Term.rename, term, Environment.get_pull]
   | closed body => rfl
   | _ => simp_all only [Term.rename, term, Environment.pull_lift]

def PureSubstitution {interp : Named.Interp} (σ : Substitution Γ Δ)
    (target : Environment Δ interp) (source : Environment Γ interp) : Prop :=
  ∀ {t} (v : Var Γ t), term (σ v) target = (getVariable v source, true)

theorem PureSubstitution.lift {interp : Named.Interp} {σ : Substitution Γ Δ}
    {target : Environment Δ interp} {source : Environment Γ interp}
    (pure : PureSubstitution σ target source) (value : Model a interp) :
    PureSubstitution σ.lift (value, target) (value, source) := by
  intro t v
  cases v with
  | here => rfl
  | there v =>
    simp only [Substitution.lift, term_rename, Environment.pull_there, getVariable]
    exact pure v

namespace Environment
 def evalSubstitution {interp : Named.Interp} (σ : Substitution Γ Δ) (target : Environment Δ interp) : Environment Γ interp :=
   ofLookup Γ (fun v => (term (σ v) target).1)
 theorem get_evalSubstitution {interp : Named.Interp} (σ : Substitution Γ Δ) (target : Environment Δ interp) (v : Var Γ t) :
   getVariable v (evalSubstitution σ target) = (term (σ v) target).1 := get_ofLookup _ v
 theorem evalSubstitution_lift {interp : Named.Interp} (σ : Substitution Γ Δ) (target : Environment Δ interp) (value : Model a interp) :
   evalSubstitution σ.lift (value, target) = (value, evalSubstitution σ target) := by
   apply ext; intro t v
   rw [get_evalSubstitution]
   cases v with
   | here => rfl
   | there v =>
     simp only [Substitution.lift, term_rename, pull_there, getVariable]
     exact (get_evalSubstitution σ target v).symm
end Environment

def SubstitutionSafe {interp : Named.Interp} (σ : Substitution Γ Δ) (target : Environment Δ interp) : Prop :=
  ∀ {t} (v : Var Γ t), (term (σ v) target).2 = true

theorem SubstitutionSafe.lift {interp : Named.Interp} {σ : Substitution Γ Δ}
    {target : Environment Δ interp} (safe : SubstitutionSafe σ target) (value : Model a interp) :
    SubstitutionSafe σ.lift (value, target) := by
  intro t v; cases v with
  | here => rfl
  | there v => simpa only [Substitution.lift, term_rename, Environment.pull_there] using safe v

/-- Pure substitutions introduce no guards and preserve all guards in the
substituted body, including the guards of callbacks and shared functions. -/
theorem term_substituteSafe {interp : Named.Interp} (body : Term Γ t) (σ : Substitution Γ Δ)
    (target : Environment Δ interp) (safe : SubstitutionSafe σ target) :
    term (body.substitute σ) target = term body (Environment.evalSubstitution σ target) := by
  induction body generalizing Δ with
  | var v =>
    apply Prod.ext
    · exact (Environment.get_evalSubstitution σ target v).symm
    · exact safe v
  | closed body => rfl
  | _ => simp_all only [Term.substitute, term, Environment.evalSubstitution_lift, SubstitutionSafe.lift]

theorem term_substitute {interp : Named.Interp} (body : Term Γ t) (σ : Substitution Γ Δ)
    (target : Environment Δ interp) (source : Environment Γ interp)
    (pure : PureSubstitution σ target source) : term (body.substitute σ) target = term body source := by
  have safe : SubstitutionSafe σ target := fun v => congrArg Prod.snd (pure v)
  have equal : Environment.evalSubstitution σ target = source := by
    apply Environment.ext; intro t v
    rw [Environment.get_evalSubstitution, pure v]
  rw [term_substituteSafe body σ target safe, equal]

def packEnvironment {interp : Named.Interp} : {Γ : List Core.Ty} → Environment Γ interp → Model (environmentType Γ) interp
  | [], _ => ()
  | _ :: _, (head, tail) => (head, packEnvironment tail)

theorem term_project {interp : Named.Interp} (tuple : Term Δ (environmentType Γ))
    (env : Environment Δ interp) (captured : Environment Γ interp)
    (equal : term tuple env = (packEnvironment captured, true)) (v : Var Γ t) :
    term (project tuple v) env = (getVariable v captured, true) := by
  induction v generalizing Δ with
  | here =>
    change ((term tuple env).1.1, (term tuple env).2) = (captured.1, true)
    rw [equal]
    rfl
  | there v ih =>
    apply ih (.snd tuple) env captured.2
    change ((term tuple env).1.2, (term tuple env).2) = (packEnvironment captured.2, true)
    rw [equal]
    rfl

/-- Applying an abstracted continuation preserves its actual invocation guard.
No continuation is inlined and no whole-source execution is assumed. -/
theorem term_abstract_apply {interp : Named.Interp} (body : Term Γ t)
    (env : Environment Δ interp) (captured : Environment Γ interp) :
    (term (body.abstract : Term Δ (.fn (environmentType Γ) t)) env).1 (packEnvironment captured) = term body captured := by
  simp only [Term.abstract, term]
  apply term_substitute
  intro u v
  exact term_project (.var (.here : Var [environmentType Γ] (environmentType Γ)))
    (packEnvironment captured, ()) captured rfl v

theorem term_abstract_safe {interp : Named.Interp} (body : Term Γ t) (env : Environment Δ interp) :
    (term (body.abstract : Term Δ (.fn (environmentType Γ) t)) env).2 = true := rfl
end Ariadne.Shallow.Safety
