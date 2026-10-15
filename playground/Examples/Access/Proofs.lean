import Examples.Access
import Ariadne.Lib.Map

/-!
# Proofs about access control

The class `Access` becomes the record `«Access»` of its two maps, and each method a function on it.
The generated frame lemmas say which fields a method never writes: `grant`, `revoke` and `claim` keep
`suspended`. From these, suspension is permanent, whatever sequence of operations follows.
-/

namespace Examples.Access.Proofs
open Ariadne Examples.Access

/-- Writers can read. -/
theorem canRead_of_canWrite (a : «Access») (u : JSString) (h : «canWrite» a u = true) : «canRead» a u = true := by
  unfold «canWrite» at h
  unfold «canRead»
  cases hs : (mapGet a.«suspended» u).isSome <;> cases hr : mapGet a.«roles» u <;> simp_all

/-- Owners can write. -/
theorem canWrite_of_isOwner (a : «Access») (u : JSString) (h : «isOwner» a u = true) : «canWrite» a u = true := by
  unfold «isOwner» at h
  unfold «canWrite»
  cases hs : (mapGet a.«suspended» u).isSome <;> cases hr : mapGet a.«roles» u <;> simp_all

/-- A suspended user can do nothing. -/
theorem suspended_locked (a : «Access») (u : JSString) (h : (mapGet a.«suspended» u).isSome) :
    «canRead» a u = false ∧ «canWrite» a u = false ∧ «isOwner» a u = false := by
  simp [«canRead», «canWrite», «isOwner», h]

/-- Only owners change the roles: a `grant` by anyone else leaves the state as it was. -/
theorem grant_needs_owner (a : «Access») (by_ u : JSString) (r : «Role») (h : «isOwner» a by_ = false) :
    «grant» a by_ u r = a := by
  simp [«grant», h]

/-- Owners cannot revoke their own access (so a document never loses its last owner this way). -/
theorem revoke_self (a : «Access») (u : JSString) : «revoke» a u u = a := by
  simp [«revoke»]

/-- The first user to claim a new document owns it. -/
theorem claim_new (u : JSString) : «isOwner» («claim» «new Access» u) u = true := by
  simp [«claim», «isOwner», «new Access», mapGet_mapPut, mapGet_nil, readable]

/-- A document with roles cannot be claimed. -/
theorem claim_taken (a : «Access») (u : JSString) (h : a.«roles» ≠ []) : «claim» a u = a := by
  simp [«claim», h]

/-! ## Suspension is permanent -/

/-- The operations that change the state. -/
inductive Op where
  | grant (by_ user : JSString) (role : «Role»)
  | revoke (by_ user : JSString)
  | suspend (by_ user : JSString)
  | claim (user : JSString)

/-- An operation's effect: the method's readable definition. -/
def Op.apply (a : «Access») : Op → «Access»
  | .grant b u r => Examples.Access.«grant» a b u r
  | .revoke b u => Examples.Access.«revoke» a b u
  | .suspend b u => Examples.Access.«suspend» a b u
  | .claim u => Examples.Access.«claim» a u

/-- No operation lifts a suspension: three of them never write `suspended` (the generated frame
lemmas), and `suspend` only adds to it. -/
theorem apply_keeps_suspended (a : «Access») (u : JSString) (op : Op) (h : (mapGet a.«suspended» u).isSome) :
    (mapGet (op.apply a).«suspended» u).isSome := by
  cases op with
  | grant b v r => rw [Op.apply, «grant».keeps.«suspended»]; exact h
  | revoke b v => rw [Op.apply, «revoke».keeps.«suspended»]; exact h
  | claim v => rw [Op.apply, «claim».keeps.«suspended»]; exact h
  | suspend b v =>
    simp only [Op.apply, Examples.Access.«suspend»]
    split
    · exact h
    · simp only [readable, mapGet_mapPut]
      split <;> simp_all

/-- **Suspension is permanent.** After any sequence of operations, a suspended user still can do
nothing. -/
theorem suspended_forever (a : «Access») (u : JSString) (ops : List Op) (h : (mapGet a.«suspended» u).isSome) :
    let a' := ops.foldl Op.apply a
    «canRead» a' u = false ∧ «canWrite» a' u = false ∧ «isOwner» a' u = false := by
  apply suspended_locked
  induction ops generalizing a with
  | nil => exact h
  | cons op ops ih => exact ih _ (apply_keeps_suspended a u op h)

/-- **The claim about the JavaScript.** Every run of `suspend` on a state and arguments representing
its inputs converges to the state the definition gives. -/
theorem suspend_runs (a : «Access») (by_ u : JSString) (this' : JSValue) (vs : List JSValue)
    (args : ArgsRep sig.«suspend».params (this' :: vs) (a, by_, u, ())) :
    ∃ w t, Converges (fun fuel => runMethod ast fuel "suspend" this' vs) (.ok (w, t)) ∧
      Ty.Rep ty.«Access» t («suspend» a by_ u) :=
  «suspend».source a by_ u this' vs args

end Examples.Access.Proofs
