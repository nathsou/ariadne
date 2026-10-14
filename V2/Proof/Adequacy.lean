import V2.Proof.Trivial
import V2.Proof.Store

/-!
# Adequacy

**The theorem.** In a well-formed typed program, every function, run by the model
on any JavaScript arguments representing inputs on which it is safe, converges
to a value representing its denotation.
-/

set_option linter.unusedSimpArgs false

namespace V2

/-- `prog` resolves each function of `P` to its erasure. -/
def Lookups (prog : Program) : TProgram Φ → Prop
  | .nil => True
  | .cons s body rest =>
    prog.find? (·.name == s.name) =
        some { name := s.name, params := s.params.map Prod.fst, body := body.erase, method := s.method } ∧
      Lookups prog rest

theorem TProgram.fnsOK {prog : Program} : ∀ {Φ : Sigs} (P : TProgram Φ), Lookups prog P → P.bodiesOk = true →
    FnsOK prog P.denote P.safety
  | _, .nil, _, _ => ⟨fun v => (nomatch v), fun v => (nomatch v), fun v => (nomatch v)⟩
  | _, .cons s body rest, h, hok => by
    obtain ⟨hfind, hrest⟩ := h
    simp only [TProgram.bodiesOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨⟨⟨⟨⟨⟨hwf, hvm⟩, hfalls⟩, hbreaks⟩, hconts⟩, _⟩, hok2⟩ := hok
    have ih : FnsOK prog rest.denote rest.safety := rest.fnsOK hrest hok2
    have hbody : ∀ xs, body.safeFn rest.denote rest.safety xs = true →
        body.safe rest.denote rest.safety (K.all fun _ => true) xs = true := by
      intro xs h
      unfold TStmts.safeFn at h
      split at h
      · exact TStmts.safe_of_trivial body _ xs (fun _ => ⟨rfl, rfl, rfl⟩) (by assumption)
      · exact h
    -- The body returns on every path.
    have hrun : ∀ xs vs, ArgsRep s.params vs xs → body.safeFn rest.denote rest.safety xs = true →
        ∃ w e N, (∀ m, N ≤ m → execStmts prog m (bindParams (s.params.map Prod.fst) vs) body.erase =
          .ok (.returned w e)) ∧ RetRel s.result s.void w e (body.denoteFn rest.denote xs) := by
      intro xs vs hargs hsafe
      obtain ⟨out, ⟨N, hc⟩, hr⟩ := TStmts.adequate ih (rest.safeSigs hok2) body (K.all fun _ => Ty.default _)
        (K.all fun _ => true) hargs (hbody xs hsafe) hwf
      cases out with
      | returned w e => exact ⟨w, e, N, hc, hr⟩
      | normal _ => simp [SRel, hfalls] at hr
      | broke _ => simp [SRel, hbreaks] at hr
      | continued _ => simp [SRel, hconts] at hr
    refine ⟨fun v xs vs hv hargs hsafe => ?_, fun v xs vs hv hargs hsafe => ?_, fun v => ?_⟩
    · cases v with
      | there v => exact ih.conv v xs vs hv hargs hsafe
      | here =>
        obtain ⟨w, e, N, hc, hr⟩ := hrun xs vs hargs hsafe
        simp only [hv, RetRel] at hr
        exact ⟨w, Converges.of_succ N fun m hm => by simp [call, hfind, hc m hm, bind, Except.bind], hr⟩
    · cases v with
      | there v => exact ih.convState v xs vs hv hargs hsafe
      | here =>
        obtain ⟨w, e, N, hc, hr⟩ := hrun xs vs hargs hsafe
        simp only [hv, RetRel] at hr
        obtain ⟨t, hl, ht⟩ := hr
        have hm : s.method = true := by simpa [hv] using hvm
        exact ⟨w, t, Converges.of_succ N fun m hm' => by
          simp [callState, hfind, hm, hc m hm', thisOf, hl, bind, Except.bind, pure, Except.pure], ht⟩
    · cases v with
      | there v => exact ih.mem v
      | here => exact List.any_eq_true.mpr ⟨_, List.mem_of_find?_eq_some hfind, by simp [List.find?_some hfind]⟩

theorem Lookups.append {prog : Program} (more : Program) : ∀ {Φ : Sigs} {P : TProgram Φ},
    Lookups prog P → Lookups (prog ++ more) P
  | _, .nil, _ => trivial
  | _, .cons _ _ _, h => by
    obtain ⟨h, rest⟩ := h
    exact show _ ∧ _ from ⟨by simp [List.find?_append, h], rest.append more⟩

theorem TProgram.erase_names : ∀ {Φ : Sigs} (P : TProgram Φ), P.erase.map (·.name) = P.names.reverse
  | _, .nil => rfl
  | _, .cons _ _ rest => by simp [TProgram.erase, TProgram.names, rest.erase_names]

theorem TProgram.lookups : ∀ {Φ : Sigs} (P : TProgram Φ), P.names.Nodup → Lookups P.erase P
  | _, .nil, _ => trivial
  | _, .cons s body rest, nodup => by
    simp only [TProgram.names, List.nodup_cons] at nodup
    refine show _ ∧ _ from ⟨?_, (rest.lookups nodup.2).append _⟩
    have hnone : rest.erase.find? (·.name == s.name) = none := by
      rw [List.find?_eq_none]
      intro fn mem heq
      apply nodup.1
      have : fn.name ∈ rest.erase.map (·.name) := List.mem_map_of_mem mem
      rw [rest.erase_names, List.mem_reverse] at this
      simpa using (beq_iff_eq.mp heq) ▸ this
    simp [TProgram.erase, List.find?_append, hnone]

/-- Well-formedness from the static check of the erased program (which already
requires distinct names) and the bodies' check: what a printed file proves, so the
kernel does not erase the program again or compare its names twice. -/
theorem TProgram.wf_of {Φ : Sigs} (P : TProgram Φ) {ast : Program} (erased : P.erase = ast)
    (bodies : P.bodiesOk = true) (hs : ast.scoped = true) : P.WF := by
  subst erased
  refine ⟨?_, bodies, hs⟩
  have h := hs
  simp only [Program.scoped, Bool.and_eq_true] at h
  have := distinct_iff.mp h.1
  rw [P.erase_names, List.Nodup, List.pairwise_reverse] at this
  exact this.imp fun h e => h e.symm

/-- **Adequacy.** In a well-formed typed program, every function, run by the model
on arguments representing inputs on which it is safe, converges to a value
representing its denotation. -/
theorem adequacy {Φ : Sigs} (P : TProgram Φ) (wf : P.WF) {f : String} {s : Sig} (v : FVar Φ f s)
    (hv : s.void = false) (xs : s.params.denote) (vs : List JSValue) (args : ArgsRep s.params vs xs)
    (safe : v.safe P.safety xs = true) :
    ∃ w, Converges (fun n => run P.erase n f vs) (.ok w) ∧ s.result.Rep w (v.get P.denote xs) := by
  simpa only [run, wf.2.2, ite_true] using (P.fnsOK (P.lookups wf.1) wf.2.1).conv v xs vs hv args safe

/-- **Adequacy for methods that change the state.** Called on a state and arguments
representing safe inputs, such a method converges to a state representing its
denotation. -/
theorem adequacy_state {Φ : Sigs} (P : TProgram Φ) (wf : P.WF) {f : String} {s : Sig} (v : FVar Φ f s)
    (hv : s.void = true) (xs : s.params.denote) (this : JSValue) (vs : List JSValue)
    (args : ArgsRep s.params (this :: vs) xs) (safe : v.safe P.safety xs = true) :
    ∃ w t, Converges (fun n => runMethod P.erase n f this vs) (.ok (w, t)) ∧ s.result.Rep t (v.get P.denote xs) := by
  simpa only [runMethod, wf.2.2, ite_true] using (P.fnsOK (P.lookups wf.1) wf.2.1).convState v xs _ hv args safe

/-- Adequacy for a printed file: its source AST, and its functions and safety
conditions as the readable definitions `fs` and `ss`. -/
theorem source_of {Φ : Sigs} {P : TProgram Φ} {ast : Program} {fs : Φ.denote} {ss : Φ.safety}
    (erased : P.erase = ast) (wf : P.WF) (denote_eq : P.denote = fs) (safety_eq : P.safety = ss) {f : String}
    {s : Sig} (v : FVar Φ f s) (hv : s.void = false) (xs : s.params.denote) (vs : List JSValue)
    (args : ArgsRep s.params vs xs) (safe : v.safe ss xs = true) :
    ∃ w, Converges (fun n => run ast n f vs) (.ok w) ∧ s.result.Rep w (v.get fs xs) := by
  subst erased; subst denote_eq; subst safety_eq
  exact adequacy P wf v hv xs vs args safe

/-- Adequacy for a printed file's methods that change the state. -/
theorem source_state_of {Φ : Sigs} {P : TProgram Φ} {ast : Program} {fs : Φ.denote} {ss : Φ.safety}
    (erased : P.erase = ast) (wf : P.WF) (denote_eq : P.denote = fs) (safety_eq : P.safety = ss) {f : String}
    {s : Sig} (v : FVar Φ f s) (hv : s.void = true) (xs : s.params.denote) (this : JSValue) (vs : List JSValue)
    (args : ArgsRep s.params (this :: vs) xs) (safe : v.safe ss xs = true) :
    ∃ w t, Converges (fun n => runMethod ast n f this vs) (.ok (w, t)) ∧ s.result.Rep t (v.get fs xs) := by
  subst erased; subst denote_eq; subst safety_eq
  exact adequacy_state P wf v hv xs this vs args safe

/-- Adequacy for methods that change the state, in the store model: the object is
changed in place and shared with the methods it calls (`runMethod_store`). -/
theorem adequacy_state_store {Φ : Sigs} (P : TProgram Φ) (wf : P.WF) {f : String} {s : Sig} (v : FVar Φ f s)
    (hv : s.void = true) (xs : s.params.denote) (this : JSValue) (vs : List JSValue)
    (args : ArgsRep s.params (this :: vs) xs) (safe : v.safe P.safety xs = true) :
    ∃ w t, Converges (fun n => runMethodStore P.erase n f this vs) (.ok (w, t)) ∧
      s.result.Rep t (v.get P.denote xs) := by
  simpa only [runMethod_store] using adequacy_state P wf v hv xs this vs args safe

end V2
