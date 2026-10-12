import Ariadne.Certificate
import Ariadne.Heap

namespace Ariadne

/-- A call starting from an explicit state, including class method receivers.
Input validity belongs to the representation relation used by an adequacy
theorem; this predicate itself only records operational execution. -/
def Invokes (program : Program) (before : State) (target : Value) (args : List Value)
    (value : Value) (after : State) : Prop :=
  Converges (fun fuel => apply program fuel before target args) (.ok (value, after))

theorem Invokes.deterministic {program : Program} {before : State} {target : Value}
    {args : List Value} {a b : Value} {sa sb : State}
    (ha : Invokes program before target args a sa)
    (hb : Invokes program before target args b sb) : a = b ∧ sa = sb := by
  have same := converges_deterministic _ (fun h => apply_fuel_mono program h before target args) ha hb
  exact Prod.mk.inj (Except.ok.inj same)

theorem Invokes.eventually {program : Program} {before : State} {target : Value}
    {args : List Value} {value : Value} {after : State}
    (h : Invokes program before target args value after) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel →
      apply program fuel before target args = .ok (value, after) :=
  ((converges_iff_eventually _ (fun h => apply_fuel_mono program h before target args) _).mp h).2

/-- Source-bound execution preserves the final state for subsequent calls. -/
def SourceInvokes (source : String) (before : State) (target : Value) (args : List Value)
    (value : Value) (after : State) : Prop :=
  ∃ program, frontend source = .ok program ∧ Invokes program before target args value after

def SourceReturnsFrom (source name : String) (heap : Heap) (args : List Value) (value : Value) : Prop :=
  ∃ after, SourceInvokes source { heap } (.function name) args value after

theorem Certificate.transfer_invocation {source : String} (certificate : Certificate source)
    {before : State} {target : Value} {args : List Value} {value : Value} {after : State}
    (h : Invokes certificate.program before target args value after) :
    SourceInvokes source before target args value after := ⟨_, certificate.checked, h⟩

theorem Certificate.transfer_from {source : String} (certificate : Certificate source)
    {name : String} {heap : Heap} {args : List Value} {value : Value} {after : State}
    (h : Invokes certificate.program { heap } (.function name) args value after) :
    SourceReturnsFrom source name heap args value := ⟨after, certificate.transfer_invocation h⟩

theorem SourceInvokes.deterministic {source : String} {before : State} {target : Value}
    {args : List Value} {a b : Value} {sa sb : State}
    (ha : SourceInvokes source before target args a sa)
    (hb : SourceInvokes source before target args b sb) : a = b ∧ sa = sb := by
  rcases ha with ⟨p, hp, ha⟩
  rcases hb with ⟨q, hq, hb⟩
  have same : p = q := Except.ok.inj (hp.symm.trans hq)
  subst q
  exact ha.deterministic hb

theorem SourceReturnsFrom.deterministic {source name : String} {heap : Heap} {args : List Value}
    {a b : Value} (ha : SourceReturnsFrom source name heap args a)
    (hb : SourceReturnsFrom source name heap args b) : a = b := by
  rcases ha with ⟨_, ha⟩
  rcases hb with ⟨_, hb⟩
  exact (ha.deterministic hb).1

theorem sourceReturnsFrom_empty_iff {source name : String} {args : List Value} {value : Value} :
    SourceReturnsFrom source name [] args value ↔ SourceReturns source name args value := by
  constructor
  · rintro ⟨after, p, hp, _, fuel, h⟩
    refine ⟨p, hp, fuel, ?_⟩
    simp only [run, runState, h, Except.map]
  · rintro ⟨p, hp, fuel, h⟩
    unfold run at h
    cases hr : runState p name fuel args with
    | error err => simp [hr, Except.map] at h
    | ok result =>
      rcases result with ⟨actual, after⟩
      simp only [hr, Except.map, Except.ok.injEq] at h
      subst actual
      exact ⟨after, p, hp, (by intro h; cases h), fuel, hr⟩

end Ariadne
