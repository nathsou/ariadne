import Ariadne.Proof.Stmt
import Ariadne.Eqns.Stmt
import Ariadne.Lib.Loop

/-!
# Frames

Which fields of the state a method leaves alone. `TProgram.frames g` marks, per function, a method
that never writes the state's field `g`: it neither sets nor deletes in `this.g`, and every method it
calls is marked. `frame_of` turns a mark into an equation about the readable definition:
`(m this args).g = this.g`.

The check is syntactic and the proof is general: over any run of a marked body, every variable
named `this` keeps `g`'s value (`Ctx.Keeps`), so the state the method returns does. A generated file
proves the marks by evaluation (`decide`), one list per field.
-/

set_option linter.unusedSectionVars false

namespace Ariadne

/-! ## The check -/

/-- The mark of the function a reference names, in a list of marks aligned with the signatures. -/
def FVar.flag : FVar Φ f s → List Bool → Bool
  | .here, b :: _ => b
  | .there v, _ :: bs => v.flag bs
  | _, _ => false

mutual
  /-- The statements never write the state's field `g`, given marks `known` for the functions in scope;
  `nk`, `bk` and `ck` say whether completing normally, breaking or continuing reaches code that does
  not either. -/
  def TStmts.keeps (g : String) (known : List Bool) : TStmts Φ Γ τ → Bool → Bool → Bool → Bool
    | .nil, nk, _, _ => nk
    | .const x _ rest, nk, bk, ck | .let_ x _ rest, nk, bk, ck => x != "this" && rest.keeps g known nk bk ck
    | .ret _ _, _, _, _ => false
    | .ite _ yes no rest, nk, bk, ck =>
      let r := rest.keeps g known nk bk ck
      yes.keeps g known r bk ck && no.keeps g known r bk ck
    | .block body rest, nk, bk, ck => body.keeps g known (rest.keeps g known nk bk ck) bk ck
    | .brk _, _, bk, _ => bk
    | .assign (x := x) _ _ rest, nk, bk, ck => x != "this" && rest.keeps g known nk bk ck
    | .cont _, _, _, ck => ck
    | .forOf x _ body rest, nk, bk, ck => x != "this" && rest.keeps g known nk bk ck && body.keeps g known true true true
    | .forEntries i x _ body rest, nk, bk, ck =>
      i != "this" && x != "this" && rest.keeps g known nk bk ck && body.keeps g known true true true
    | .ifNull (x := x) _ _ yes no rest, nk, bk, ck | .ifNotNull (x := x) _ _ yes no rest, nk, bk, ck =>
      let r := rest.keeps g known nk bk ck
      x != "this" && yes.keeps g known r bk ck && no.keeps g known r bk ck
    | .ifNullExit (x := x) _ _ yes rest, nk, bk, ck =>
      x != "this" && yes.keeps g known nk bk ck && rest.keeps g known nk bk ck
    | .switchG (x := x) _ _ arms rest, nk, bk, ck =>
      let r := rest.keeps g known nk bk ck
      x != "this" && r && arms.keeps g known r r ck
    | .forRange i _ body rest, nk, bk, ck => i != "this" && rest.keeps g known nk bk ck && body.keeps g known true true true
    | .stateSet (f := f) _ _ _ _ _ rest, nk, bk, ck | .stateDelete (f := f) _ _ _ _ rest, nk, bk, ck =>
      f != g && rest.keeps g known nk bk ck
    | .callVoid fn _ _ rest, nk, bk, ck => fn.flag known && rest.keeps g known nk bk ck
    | .retVoid _ _, _, _, _ => true

  def TArms.keeps {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
      (g : String) (known : List Bool) : TArms Φ Γ τ v → Bool → Bool → Bool → Bool
    | .nil, nk, _, _ => nk
    | .empty _ rest, nk, bk, ck => rest.keeps g known nk bk ck
    | .wide _ body rest, nk, bk, ck => body.keeps g known nk bk ck && rest.keeps g known nk bk ck
    | .narrow _ body rest, nk, bk, ck => nk && body.keeps g known nk bk ck && rest.keeps g known nk bk ck
end

/-- Per function, newest first: a method that never writes the state's field `g`. -/
def TProgram.frames (g : String) : TProgram Φ → List Bool
  | .nil => []
  | .cons s body rest =>
    let known := rest.frames g
    (s.params.tail.all (·.1 != "this") && body.keeps g known false false false) :: known

/-! ## Invariants -/

section
variable {fs0 : Fields} {g : String} {φ : Ty} (j : FIdx fs0 g φ) (c : φ.denote)

/-- A value of type `τ` that, if `τ` is the state's type, has `c` in field `g`. -/
def Ty.Keeps (τ : Ty) (a : τ.denote) : Prop :=
  ∀ h : τ = .record fs0, j.get (cast (congrArg Ty.denote h) a) = c

/-- Every variable named `this` keeps `c` in field `g`. -/
def Ctx.Keeps : (Γ : Ctx) → Γ.denote → Prop
  | [], _ => True
  | (x, τ) :: Γ, (a, ρ) => (x = "this" → Ty.Keeps j c τ a) ∧ Ctx.Keeps Γ ρ

/-- The first parameter, if named `this`, keeps `c` in field `g`. -/
def Ctx.Head : (Γ : Ctx) → Γ.denote → Prop
  | [], _ => True
  | (x, τ) :: _, (a, _) => x = "this" → Ty.Keeps j c τ a

/-- Continuations that, from an environment keeping `c`, give a result keeping it (when reached). -/
def K.Keeps {Γ : Ctx} {τ : Ty} (nk bk ck : Bool) (k : K Γ τ.denote) : Prop :=
  ∀ ρ, Ctx.Keeps j c Γ ρ → (nk = true → Ty.Keeps j c τ (k.normal ρ)) ∧ (bk = true → Ty.Keeps j c τ (k.brk ρ)) ∧
    (ck = true → Ty.Keeps j c τ (k.cont ρ))

/-- The function leaves field `g` of the state it is given. -/
def Frame (s : Sig) (f : s.denote) : Prop :=
  ∀ (c : φ.denote) (a : s.params.denote), Ctx.Head j c s.params a → Ty.Keeps j c s.result (f a)

theorem FIdx.get_set_ne : ∀ {fs : Fields} {f g : String} {τ σ : Ty} (i : FIdx fs f τ) (j : FIdx fs g σ)
    (r : fs.denote) (y : τ.denote), f ≠ g → j.get (i.set r y) = j.get r
  | .cons .., _, _, _, _, .here, .here, _, _, h => absurd rfl h
  | .cons .., _, _, _, _, .here, .there _, _, _, _ => rfl
  | .cons .., _, _, _, _, .there _, .here, _, _, _ => rfl
  | .cons .., _, _, _, _, .there i, .there j, (_, r), y, h => FIdx.get_set_ne i j r y h

theorem Var.get_keeps : ∀ {Γ : Ctx} {x : String} {τ : Ty} (v : Var Γ x τ) (ρ : Γ.denote), x = "this" →
    Ctx.Keeps j c Γ ρ → Ty.Keeps j c τ (v.get ρ)
  | _ :: _, _, _, .here, (_, _), hx, h => h.1 hx
  | _ :: _, _, _, .there _ v, (_, ρ), hx, h => Var.get_keeps v ρ hx h.2

theorem Ctx.keeps_set : ∀ {Γ : Ctx} {x : String} {τ : Ty} (v : Var Γ x τ) (ρ : Γ.denote) (a : τ.denote),
    Ctx.Keeps j c Γ ρ → (x = "this" → Ty.Keeps j c τ a) → Ctx.Keeps j c Γ (v.set ρ a)
  | _ :: _, _, _, .here, (_, _), _, h, ha => ⟨ha, h.2⟩
  | _ :: _, _, _, .there _ v, (_, ρ), a, h, ha => ⟨h.1, Ctx.keeps_set v ρ a h.2 ha⟩

theorem Ctx.keeps_narrowVal : ∀ {Γ : Ctx} {x : String} {τ σ : Ty} (v : Var Γ x τ) (ρ : Γ.denote) (y : σ.denote),
    x ≠ "this" → Ctx.Keeps j c Γ ρ → Ctx.Keeps j c (v.narrow σ) (v.narrowVal ρ y)
  | _ :: _, _, _, _, .here, (_, _), _, hx, h => ⟨fun h' => absurd h' hx, h.2⟩
  | _ :: _, _, _, _, .there _ v, (_, ρ), y, hx, h => ⟨h.1, Ctx.keeps_narrowVal v ρ y hx h.2⟩

theorem Ctx.keeps_widen : ∀ {Γ : Ctx} {x : String} {τ σ : Ty} (v : Var Γ x τ) (e : σ.denote → τ.denote)
    (ρ : (v.narrow σ).denote), x ≠ "this" → Ctx.Keeps j c (v.narrow σ) ρ → Ctx.Keeps j c Γ (v.widen e ρ)
  | _ :: _, _, _, _, .here, _, _, hx, h => ⟨fun h' => absurd h' hx, h.2⟩
  | _ :: _, _, _, _, .there _ v, e, ρ, hx, h => ⟨h.1, Ctx.keeps_widen v e ρ.2 hx h.2⟩

theorem Ctx.keeps_of_names : ∀ (Γ : Ctx) (ρ : Γ.denote), Γ.all (·.1 != "this") = true → Ctx.Keeps j c Γ ρ
  | [], _, _ => trivial
  | _ :: Γ, (_, ρ), h => by
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ⟨fun h' => absurd h' h.1, Ctx.keeps_of_names Γ ρ (by simpa using h.2)⟩

theorem Ctx.keeps_of_head : ∀ (Γ : Ctx) (ρ : Γ.denote), Ctx.Head j c Γ ρ → Γ.tail.all (·.1 != "this") = true →
    Ctx.Keeps j c Γ ρ
  | [], _, _, _ => trivial
  | _ :: Γ, (_, ρ), h, ht => ⟨h, Ctx.keeps_of_names j c Γ ρ ht⟩

/-- A state update in a field other than `g` keeps it. -/
theorem Ty.keeps_set {fs : Fields} {f : String} {σ : Ty} (i : FIdx fs f σ) (r : fs.denote) (y : σ.denote) (hf : f ≠ g)
    (h : Ty.Keeps j c (.record fs) r) : Ty.Keeps j c (.record fs) (i.set r y) := by
  intro he
  cases he
  have := h rfl
  simp only [cast_eq] at this ⊢
  rw [FIdx.get_set_ne i j r y hf, this]

end

/-! ## Marked bodies keep the field -/

section
variable {Φ : Sigs} {fs : Φ.denote} {fs0 : Fields} {g : String} {φ : Ty} (j : FIdx fs0 g φ) (c : φ.denote)
  {known : List Bool}
  (hfn : ∀ {m : String} {s : Sig} (fn : FVar Φ m s), fn.flag known = true → Frame j s (fn.get fs))
include hfn

mutual
  theorem TStmts.keeps_spec : ∀ {Γ : Ctx} {τ : Ty} (st : TStmts Φ Γ τ) (nk bk ck : Bool) (k : K Γ τ.denote)
      (ρ : Γ.denote), st.keeps g known nk bk ck = true → K.Keeps j c nk bk ck k → Ctx.Keeps j c Γ ρ →
      Ty.Keeps j c τ (st.denote fs k ρ)
    | _, _, .nil, _, _, _, _, ρ, h, hk, hρ => (hk ρ hρ).1 h
    | _, _, .brk _, _, _, _, _, ρ, h, hk, hρ => (hk ρ hρ).2.1 h
    | _, _, .cont _, _, _, _, _, ρ, h, hk, hρ => (hk ρ hρ).2.2 h
    | _, _, .ret _ _, _, _, _, _, _, h, _, _ => by simp [TStmts.keeps] at h
    | _, _, .retVoid v _, _, _, _, _, ρ, _, _, hρ => Var.get_keeps j c v ρ rfl hρ
    | _, _, .const _ e rest, nk, bk, ck, k, ρ, h, hk, hρ | _, _, .let_ _ e rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact TStmts.keeps_spec rest nk bk ck _ _ h.2 (fun ρ' hρ' => hk ρ'.2 hρ'.2)
        ⟨fun h' => absurd h' h.1, hρ⟩
    | _, _, .assign v e rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact TStmts.keeps_spec rest nk bk ck k _ h.2 hk (Ctx.keeps_set j c v ρ _ hρ fun h' => absurd h' h.1)
    | _, _, .ite cnd yes no rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true] at h
      have hk' : K.Keeps j c (rest.keeps g known nk bk ck) bk ck { k with normal := rest.denote fs k } :=
        fun ρ' hρ' => ⟨fun hr => TStmts.keeps_spec rest nk bk ck k ρ' hr hk hρ', (hk ρ' hρ').2⟩
      simp only [TStmts.denote]
      split
      · exact TStmts.keeps_spec yes _ bk ck _ ρ h.1 hk' hρ
      · exact TStmts.keeps_spec no _ bk ck _ ρ h.2 hk' hρ
    | _, _, .block body rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps] at h
      exact TStmts.keeps_spec body _ bk ck _ ρ h
        (fun ρ' hρ' => ⟨fun hr => TStmts.keeps_spec rest nk bk ck k ρ' hr hk hρ', (hk ρ' hρ').2⟩) hρ
    | _, _, .forOf _ a body rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      simp only [TStmts.denote]
      refine forIn_inv (Ctx.Keeps j c _) (Ty.Keeps j c _) ?_ ?_ _ ρ hρ
      · intro y next ex ρ' hρ' hn hx
        exact TStmts.keeps_spec body true true true _ _ h.2
          (fun ρ'' hρ'' => ⟨fun _ => hn _ hρ''.2, fun _ => hx _ hρ''.2, fun _ => hn _ hρ''.2⟩)
          ⟨fun h' => absurd h' h.1.1, hρ'⟩
      · exact fun ρ' hρ' => TStmts.keeps_spec rest nk bk ck k ρ' h.1.2 hk hρ'
    | _, _, .forEntries _ _ a body rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      simp only [TStmts.denote]
      refine forIn_inv (Ctx.Keeps j c _) (Ty.Keeps j c _) ?_ ?_ _ ρ hρ
      · intro p next ex ρ' hρ' hn hx
        exact TStmts.keeps_spec body true true true _ _ h.2
          (fun ρ'' hρ'' => ⟨fun _ => hn _ hρ''.2.2, fun _ => hx _ hρ''.2.2, fun _ => hn _ hρ''.2.2⟩)
          ⟨fun h' => absurd h' h.1.1.2, fun h' => absurd h' h.1.1.1, hρ'⟩
      · exact fun ρ' hρ' => TStmts.keeps_spec rest nk bk ck k ρ' h.1.2 hk hρ'
    | _, _, .forRange _ v body rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      simp only [TStmts.denote]
      refine forIn_inv (Ctx.Keeps j c _) (Ty.Keeps j c _) ?_ ?_ _ ρ hρ
      · intro y next ex ρ' hρ' hn hx
        exact TStmts.keeps_spec body true true true _ _ h.2
          (fun ρ'' hρ'' => ⟨fun _ => hn _ hρ''.2, fun _ => hx _ hρ''.2, fun _ => hn _ hρ''.2⟩)
          ⟨fun h' => absurd h' h.1.1, hρ'⟩
      · exact fun ρ' hρ' => TStmts.keeps_spec rest nk bk ck k ρ' h.1.2 hk hρ'
    | _, _, .ifNull v _ yes no rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      have hk' : K.Keeps j c (rest.keeps g known nk bk ck) bk ck { k with normal := rest.denote fs k } :=
        fun ρ' hρ' => ⟨fun hr => TStmts.keeps_spec rest nk bk ck k ρ' hr hk hρ', (hk ρ' hρ').2⟩
      simp only [TStmts.denote]
      split
      · exact TStmts.keeps_spec yes _ bk ck _ ρ h.1.2 hk' hρ
      · exact TStmts.keeps_spec no _ bk ck _ _ h.2
          (fun ρ' hρ' => hk' _ (Ctx.keeps_widen j c v _ ρ' h.1.1 hρ'))
          (Ctx.keeps_narrowVal j c v ρ _ h.1.1 hρ)
    | _, _, .ifNotNull v _ yes no rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      have hk' : K.Keeps j c (rest.keeps g known nk bk ck) bk ck { k with normal := rest.denote fs k } :=
        fun ρ' hρ' => ⟨fun hr => TStmts.keeps_spec rest nk bk ck k ρ' hr hk hρ', (hk ρ' hρ').2⟩
      simp only [TStmts.denote]
      split
      · exact TStmts.keeps_spec yes _ bk ck _ _ h.1.2
          (fun ρ' hρ' => hk' _ (Ctx.keeps_widen j c v _ ρ' h.1.1 hρ'))
          (Ctx.keeps_narrowVal j c v ρ _ h.1.1 hρ)
      · exact TStmts.keeps_spec no _ bk ck _ ρ h.2 hk' hρ
    | _, _, .ifNullExit v _ yes rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      simp only [TStmts.denote]
      split
      · exact TStmts.keeps_spec yes nk bk ck k ρ h.1.2 hk hρ
      · exact TStmts.keeps_spec rest nk bk ck _ _ h.2
          (fun ρ' hρ' => hk _ (Ctx.keeps_widen j c v _ ρ' h.1.1 hρ'))
          (Ctx.keeps_narrowVal j c v ρ _ h.1.1 hρ)
    | _, _, .switchG v _ arms rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      have hr := fun ρ' hρ' => TStmts.keeps_spec rest nk bk ck k ρ' h.1.2 hk hρ'
      obtain ⟨t, fds, i, y, hu⟩ := VIdx.decomp _ (v.get ρ)
      simp only [TStmts.denote, hu, Variants.elim_inj]
      exact TArms.keeps_spec h.1.1 arms _ _ _ _ ρ i y _ h.2
        (fun ρ' hρ' => ⟨fun _ => hr ρ' hρ', fun _ => hr ρ' hρ', (hk ρ' hρ').2.2⟩) hρ (hr ρ hρ)
    | _, _, .stateSet (f := f) v i _ key e rest, nk, bk, ck, k, ρ, h, hk, hρ
    | _, _, .stateDelete (f := f) v i _ key rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      simp only [TStmts.denote]
      exact TStmts.keeps_spec rest nk bk ck k _ h.2 hk (Ctx.keeps_set j c v ρ _ hρ fun _ =>
        Ty.keeps_set j c i _ _ h.1 (Var.get_keeps j c v ρ rfl hρ))
    | _, _, .callVoid fn v args rest, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TStmts.keeps, Bool.and_eq_true] at h
      simp only [TStmts.denote]
      exact TStmts.keeps_spec rest nk bk ck k _ h.2 hk (Ctx.keeps_set j c v ρ _ hρ fun _ =>
        hfn fn h.1 c _ (fun _ => Var.get_keeps j c v ρ rfl hρ))

  theorem TArms.first_keeps {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants}
      {v : Var Γ x (.union key vs0)} : ∀ (arms : TArms Φ Γ τ v) (nk bk ck : Bool) (k : K Γ τ.denote) (ρ : Γ.denote),
      arms.keeps g known nk bk ck = true → K.Keeps j c nk bk ck k → Ctx.Keeps j c Γ ρ →
      Ty.Keeps j c τ (arms.first fs k ρ)
    | .nil, _, _, _, _, ρ, h, hk, hρ => (hk ρ hρ).1 h
    | .empty _ rest, nk, bk, ck, k, ρ, h, hk, hρ => TArms.first_keeps rest nk bk ck k ρ h hk hρ
    | .wide _ body _, nk, bk, ck, k, ρ, h, hk, hρ => by
      simp only [TArms.keeps, Bool.and_eq_true] at h
      exact TStmts.keeps_spec body nk bk ck k ρ h.1 hk hρ
    | .narrow .., _, _, _, _, ρ, h, hk, hρ => by
      simp only [TArms.keeps, Bool.and_eq_true] at h
      exact (hk ρ hρ).1 h.1.1

  theorem TArms.keeps_spec {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants}
      {v : Var Γ x (.union key vs0)} (hx : x ≠ "this") : ∀ (arms : TArms Φ Γ τ v) (nk bk ck : Bool) (k : K Γ τ.denote)
      (ρ : Γ.denote) {t : TagLit} {fds : Fields} (i : VIdx vs0 t fds) (y : fds.denote) (d : τ.denote),
      arms.keeps g known nk bk ck = true → K.Keeps j c nk bk ck k → Ctx.Keeps j c Γ ρ → Ty.Keeps j c τ d →
      Ty.Keeps j c τ (arms.denote fs k ρ i y d)
    | .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, hd => hd
    | .empty l rest, nk, bk, ck, k, ρ, _, _, i, y, d, h, hk, hρ, hd => by
      simp only [TArms.keeps] at h
      simp only [TArms.denote]
      split
      · exact TArms.first_keeps rest nk bk ck k ρ h hk hρ
      · refine TArms.keeps_spec hx rest nk bk ck k ρ i y _ h hk hρ ?_
        split
        · exact TArms.first_keeps rest nk bk ck k ρ h hk hρ
        · exact hd
    | .wide l body rest, nk, bk, ck, k, ρ, _, _, i, y, d, h, hk, hρ, hd => by
      simp only [TArms.keeps, Bool.and_eq_true] at h
      simp only [TArms.denote]
      split
      · exact TStmts.keeps_spec body nk bk ck k ρ h.1 hk hρ
      · refine TArms.keeps_spec hx rest nk bk ck k ρ i y _ h.2 hk hρ ?_
        split
        · exact TStmts.keeps_spec body nk bk ck k ρ h.1 hk hρ
        · exact hd
    | .narrow i' body rest, nk, bk, ck, k, ρ, _, _, i, y, d, h, hk, hρ, hd => by
      simp only [TArms.keeps, Bool.and_eq_true] at h
      simp only [TArms.denote]
      split
      · exact TStmts.keeps_spec body nk bk ck _ _ h.1.2
          (fun ρ' hρ' => hk _ (Ctx.keeps_widen j c v _ ρ' hx hρ'))
          (Ctx.keeps_narrowVal j c v ρ _ hx hρ)
      · exact TArms.keeps_spec hx rest nk bk ck k ρ i y d h.2 hk hρ hd
end

end

/-! ## Programs -/

/-- Every marked function leaves field `g` of the state it is given. -/
theorem TProgram.frame {fs0 : Fields} {g : String} {φ : Ty} (j : FIdx fs0 g φ) :
    ∀ {Φ : Sigs} (P : TProgram Φ) {m : String} {s : Sig} (fn : FVar Φ m s), fn.flag (P.frames g) = true →
      Frame j s (fn.get P.denote)
  | _, .nil, _, _, fn, _ => nomatch fn
  | _, .cons s body rest, _, _, fn, h => by
    cases fn with
    | there fn => exact TProgram.frame j rest fn h
    | here =>
      simp only [FVar.flag, TProgram.frames, Bool.and_eq_true] at h
      intro c a ha
      exact TStmts.keeps_spec j c (fun fn hf => TProgram.frame j rest fn hf) body false false false _ a h.2
        (fun _ _ => ⟨nofun, nofun, nofun⟩) (Ctx.keeps_of_head j c _ a ha h.1)

/-- A marked method leaves field `g` of the state: the equation about its readable definition. -/
theorem frame_of {fs0 : Fields} {g : String} {φ : Ty} (j : FIdx fs0 g φ) {Φ : Sigs} {P : TProgram Φ}
    {fns : Φ.denote} (denote_eq : P.denote = fns) {bs : List Bool} (frames_eq : P.frames g = bs) {m name : String}
    {ps : Ctx} {t : Bool} (fn : FVar Φ m ⟨name, ("this", .record fs0) :: ps, .record fs0, t, true, true⟩)
    (hf : fn.flag bs = true) (this : fs0.denote) (args : ps.denote) :
    j.get (fn.get fns (this, args)) = j.get this := by
  subst denote_eq frames_eq
  exact TProgram.frame j P fn hf (j.get this) (this, args) (fun _ _ => rfl) rfl

end Ariadne
