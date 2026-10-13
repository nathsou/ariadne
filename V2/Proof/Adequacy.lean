import V2.Proof.Trivial

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
    prog.find? (·.name == s.name) = some { name := s.name, params := s.params.map Prod.fst, body := body.erase } ∧
      Lookups prog rest

theorem TProgram.fnsOK {prog : Program} : ∀ {Φ : Sigs} (P : TProgram Φ), Lookups prog P → P.bodiesOk = true →
    FnsOK prog P.denote P.safety
  | _, .nil, _, _ => fun v => nomatch v
  | _, .cons s body rest, h, hok => by
    obtain ⟨hfind, hrest⟩ := h
    simp only [TProgram.bodiesOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
    have ih : FnsOK prog rest.denote rest.safety := rest.fnsOK hrest hok.2
    have hbody : ∀ xs, body.safeFn rest.denote rest.safety xs = true →
        body.safe rest.denote rest.safety (K.all fun _ => true) xs = true := by
      intro xs h
      unfold TStmts.safeFn at h
      split at h
      · exact TStmts.safe_of_trivial body _ xs (fun _ => ⟨rfl, rfl, rfl⟩) (by assumption)
      · exact h
    intro v xs vs hargs hsafe
    cases v with
    | there v => exact ih v xs vs hargs hsafe
    | here =>
      obtain ⟨out, ⟨N, hc⟩, hr⟩ := TStmts.adequate ih (rest.safeSigs hok.2) body (K.all fun _ => Ty.default _) (K.all fun _ => true)
        hargs (hbody xs hsafe) hok.1.1.1.1.1
      cases out with
      | returned w =>
        refine ⟨w, Converges.of_succ N fun m hm => ?_, hr⟩
        simp [call, hfind, hc m hm, bind, Except.bind]
      | normal _ => simp [SRel, hok.1.1.1.1.2] at hr
      | broke _ => simp [SRel, hok.1.1.1.2] at hr
      | continued _ => simp [SRel, hok.1.1.2] at hr

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

/-- **Adequacy.** In a well-formed typed program, every function, run by the model
on arguments representing inputs on which it is safe, converges to a value
representing its denotation. -/
theorem adequacy {Φ : Sigs} (P : TProgram Φ) (wf : P.WF) {f : String} {s : Sig} (v : FVar Φ f s)
    (xs : s.params.denote) (vs : List JSValue) (args : ArgsRep s.params vs xs) (safe : v.safe P.safety xs = true) :
    ∃ w, Converges (fun n => run P.erase n f vs) (.ok w) ∧ s.result.Rep w (v.get P.denote xs) := by
  simpa only [run, wf.2.2, ite_true] using P.fnsOK (P.lookups wf.1) wf.2.1 v xs vs args safe

/-- Adequacy for a printed file: its source AST, and its functions and safety
conditions as the readable definitions `fs` and `ss`. -/
theorem source_of {Φ : Sigs} {P : TProgram Φ} {ast : Program} {fs : Φ.denote} {ss : Φ.safety}
    (erased : P.erase = ast) (wf : P.WF) (denote_eq : P.denote = fs) (safety_eq : P.safety = ss) {f : String}
    {s : Sig} (v : FVar Φ f s) (xs : s.params.denote) (vs : List JSValue) (args : ArgsRep s.params vs xs)
    (safe : v.safe ss xs = true) :
    ∃ w, Converges (fun n => run ast n f vs) (.ok w) ∧ s.result.Rep w (v.get fs xs) := by
  subst erased; subst denote_eq; subst safety_eq
  exact adequacy P wf v xs vs args safe

end V2
