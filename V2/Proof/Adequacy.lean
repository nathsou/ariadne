import V2.Typed.Denote

/-!
# Adequacy

Every well-formed typed program's erasure, run by the model, converges to the
encoding of its denotation. One proof by induction on typed syntax; no per-program
reasoning.
-/

set_option linter.unusedSimpArgs false

namespace V2

/-! ## Environments -/

theorem Var.lookup : ∀ {Γ : Ctx} {x τ} (v : Var Γ x τ) (ρ : Γ.denote),
    (Γ.toEnv ρ).lookup x = some (τ.encode (v.get ρ))
  | _ :: _, _, _, .here, (_, _) => by simp [Ctx.toEnv, Var.get]
  | _ :: _, _, _, .there h v, (_, ρ) => by
    simp only [Ctx.toEnv, List.lookup, beq_eq_false_iff_ne.mpr h]; exact v.lookup ρ

theorem Ctx.toEnv_length : ∀ (Γ : Ctx) (ρ : Γ.denote), (Γ.toEnv ρ).length = Γ.length
  | [], () => rfl
  | _ :: Γ, (_, ρ) => by simp [Ctx.toEnv, Ctx.toEnv_length Γ ρ]

theorem Ctx.encode_length : ∀ (Γ : Ctx) (ρ : Γ.denote), (Γ.encode ρ).length = Γ.length
  | [], () => rfl
  | _ :: Γ, (_, ρ) => by simp [Ctx.encode, Ctx.encode_length Γ ρ]

theorem Ctx.zip_encode : ∀ (Γ : Ctx) (ρ : Γ.denote), (Γ.map Prod.fst).zip (Γ.encode ρ) = Γ.toEnv ρ
  | [], () => rfl
  | _ :: Γ, (_, ρ) => by simp [Ctx.encode, Ctx.toEnv, Ctx.zip_encode Γ ρ]

theorem restore_toEnv (Γ : Ctx) (ρ ρ' : Γ.denote) (bs : Env) :
    restore (Γ.toEnv ρ) (bs ++ Γ.toEnv ρ') = Γ.toEnv ρ' := by
  simp [restore, Ctx.toEnv_length]

theorem Ty.strictEq_encode : ∀ (τ : Ty) (a b : τ.denote),
    strictEq (τ.encode a) (τ.encode b) = .ok (τ.beq a b)
  | .bool, _, _ | .int, _, _ | .string, _, _ => rfl

/-! ## Fuel -/

/-- A run converges once every budget from some point on gives the result. -/
theorem Converges.of_succ {f : Nat → α} {a : α} (N : Nat) (h : ∀ m, N ≤ m → f (m + 1) = a) :
    Converges f a :=
  ⟨N + 1, fun m hm => by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact h k (by omega)⟩

/-! ## Expressions -/

/-- A binary operation whose operands converge. -/
theorem converges_binary {Γ : Ctx} {ρ : Γ.denote} {op : BinOp} {a b : Expr} {x y : JSValue} {r : JSValue}
    (hop : op ≠ .and ∧ op ≠ .or)
    (ha : Converges (fun n => evalExpr prog n (Γ.toEnv ρ) a) (.ok x))
    (hb : Converges (fun n => evalExpr prog n (Γ.toEnv ρ) b) (.ok y))
    (hr : binary op x y = .ok r) :
    Converges (fun n => evalExpr prog n (Γ.toEnv ρ) (.binary op a b)) (.ok r) := by
  obtain ⟨Na, ha⟩ := ha
  obtain ⟨Nb, hb⟩ := hb
  refine Converges.of_succ (max Na Nb) fun m hm => ?_
  rcases op <;> simp_all [evalExpr, ha m (by omega), hb m (by omega), bind, Except.bind, pure, Except.pure]

/-- The functions in scope run as their denotations. -/
def FnsOK {Φ : Sigs} (prog : Program) (fs : Φ.denote) : Prop :=
  ∀ {f s} (v : FVar Φ f s) (xs : s.params.denote),
    Converges (fun n => call prog n f (s.params.encode xs)) (.ok (s.result.encode (v.get fs xs)))

set_option linter.unusedSectionVars false in
section
variable {prog : Program} {Φ : Sigs} {fs : Φ.denote} (hfs : FnsOK prog fs)
include hfs

mutual
  theorem TExpr.adequate {Γ : Ctx} {τ : Ty} : ∀ (e : TExpr Φ Γ τ) (ρ : Γ.denote),
      Converges (fun n => evalExpr prog n (Γ.toEnv ρ) e.erase) (.ok (τ.encode (e.denote fs ρ)))
    | .bool b, ρ | .int n, ρ | .str s, ρ =>
      Converges.of_succ 0 fun m _ => by simp [evalExpr, TExpr.erase, TExpr.denote, Lit.value, Ty.encode]
    | .var v, ρ => Converges.of_succ 0 fun m _ => by
      simp [evalExpr, TExpr.erase, TExpr.denote, v.lookup ρ]
    | .not e, ρ => by
      obtain ⟨N, h⟩ := TExpr.adequate e ρ
      exact Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, TExpr.denote, h m hm, bind, Except.bind, unary, Ty.encode]
    | .neg e, ρ => by
      obtain ⟨N, h⟩ := TExpr.adequate e ρ
      exact Converges.of_succ N fun m hm => by
        simp [evalExpr, TExpr.erase, TExpr.denote, h m hm, bind, Except.bind, unary, Ty.encode]
    | .add a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .sub a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .mul a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .concat a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .eq a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ)
        (by simp only [binary, Ty.strictEq_encode]; rfl)
    | .ne a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ)
        (by simp only [binary, Ty.strictEq_encode]; rfl)
    | .lt a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .le a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .gt a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .ge a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .slt a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .sle a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .sgt a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .sge a b, ρ => converges_binary (by simp) (TExpr.adequate a ρ) (TExpr.adequate b ρ) rfl
    | .and a b, ρ => by
      obtain ⟨Na, ha⟩ := TExpr.adequate a ρ
      obtain ⟨Nb, hb⟩ := TExpr.adequate b ρ
      refine Converges.of_succ (max Na Nb) fun m hm => ?_
      cases hx : a.denote fs ρ <;>
        simp_all [evalExpr, TExpr.erase, TExpr.denote, ha m (by omega), hb m (by omega), bind, Except.bind,
          Ty.encode]
    | .or a b, ρ => by
      obtain ⟨Na, ha⟩ := TExpr.adequate a ρ
      obtain ⟨Nb, hb⟩ := TExpr.adequate b ρ
      refine Converges.of_succ (max Na Nb) fun m hm => ?_
      cases hx : a.denote fs ρ <;>
        simp_all [evalExpr, TExpr.erase, TExpr.denote, ha m (by omega), hb m (by omega), bind, Except.bind,
          Ty.encode]
    | .cond c a b, ρ => by
      obtain ⟨Nc, hc⟩ := TExpr.adequate c ρ
      obtain ⟨Na, ha⟩ := TExpr.adequate a ρ
      obtain ⟨Nb, hb⟩ := TExpr.adequate b ρ
      refine Converges.of_succ (max Nc (max Na Nb)) fun m hm => ?_
      cases hx : c.denote fs ρ <;>
        simp_all [evalExpr, TExpr.erase, TExpr.denote, hc m (by omega), ha m (by omega), hb m (by omega),
          bind, Except.bind, Ty.encode]
    | .call fn args, ρ => by
      obtain ⟨Na, ha⟩ := TArgs.adequate args ρ
      obtain ⟨Nc, hc⟩ := hfs fn (args.denote fs ρ)
      refine Converges.of_succ (max Na Nc) fun m hm => ?_
      simp [evalExpr, TExpr.erase, TExpr.denote, ha m (by omega), hc m (by omega), bind, Except.bind, pure, Except.pure]

  theorem TArgs.adequate {Γ ps : Ctx} : ∀ (args : TArgs Φ Γ ps) (ρ : Γ.denote),
      Converges (fun n => evalArgs prog n (Γ.toEnv ρ) args.erase) (.ok (ps.encode (args.denote fs ρ)))
    | .nil, ρ => Converges.of_succ 0 fun m _ => by simp [evalArgs, TArgs.erase, Ctx.encode]
    | .cons e rest, ρ => by
      obtain ⟨Ne, he⟩ := TExpr.adequate e ρ
      obtain ⟨Nr, hr⟩ := TArgs.adequate rest ρ
      refine Converges.of_succ (max Ne Nr) fun m hm => ?_
      simp [evalArgs, TArgs.erase, TArgs.denote, Ctx.encode, he m (by omega), hr m (by omega), bind,
        Except.bind, pure, Except.pure]
end

/-! ## Statement lists -/

/-- How a run of a statement list relates to its denotation `r` under continuation
`k`: a `return` carries the result; running to the end leaves the declarations of
the list on top of the environment, and the result is what follows. -/
def StmtsRel (Γ : Ctx) (τ : Ty) (r : τ.denote) (k : Γ.denote → τ.denote) (returns : Bool) : Outcome → Prop
  | .returned v => v = τ.encode r
  | .normal env => returns = false ∧ ∃ bs ρ', env = bs ++ Γ.toEnv ρ' ∧ r = k ρ'

theorem TStmts.adequate : ∀ {Γ : Ctx} {τ : Ty} (ss : TStmts Φ Γ τ) (k : Γ.denote → τ.denote) (ρ : Γ.denote),
    ∃ out, Converges (fun n => execStmts prog n (Γ.toEnv ρ) ss.erase) (.ok out) ∧
      StmtsRel Γ τ (ss.denote fs k ρ) k ss.returns out
  | Γ, _, .nil, k, ρ => ⟨.normal (Γ.toEnv ρ), Converges.of_succ 0 (fun m _ => by simp [execStmts, TStmts.erase]),
      rfl, [], ρ, rfl, rfl⟩
  | Γ, τ, .const x e rest, k, ρ => by
    obtain ⟨Ne, he⟩ := TExpr.adequate hfs e ρ
    obtain ⟨out, ⟨Nr, hr⟩, rel⟩ := TStmts.adequate rest (fun ρ' => k ρ'.2) (e.denote fs ρ, ρ)
    refine ⟨out, Converges.of_succ (max (Ne + 1) Nr) fun m hm => ?_, ?_⟩
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hr := hr (m' + 1) (by omega)
      simp only [Ctx.toEnv] at hr
      simp [execStmts, execStmt, TStmts.erase, he m' (by omega), hr, bind, Except.bind, pure, Except.pure]
    · cases out with
      | returned v => exact rel
      | normal env =>
        obtain ⟨hret, bs, ⟨v', ρ'⟩, rfl, hk⟩ := rel
        exact ⟨hret, bs ++ [(x, Ty.encode _ v')], ρ', by simp [Ctx.toEnv], hk⟩
  | Γ, τ, .ret e rest, k, ρ => by
    obtain ⟨Ne, he⟩ := TExpr.adequate hfs e ρ
    refine ⟨.returned (τ.encode (e.denote fs ρ)), Converges.of_succ (Ne + 1) fun m hm => ?_, rfl⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp [execStmts, execStmt, TStmts.erase, he m' (by omega), bind, Except.bind, pure, Except.pure]
  | Γ, τ, .ite c yes no rest, k, ρ => by
    obtain ⟨Nc, hc⟩ := TExpr.adequate hfs c ρ
    cases hcv : c.denote fs ρ with
    | true =>
      obtain ⟨out₁, ⟨N₁, h₁⟩, rel₁⟩ := TStmts.adequate yes (rest.denote fs k) ρ
      cases out₁ with
      | returned v =>
        refine ⟨.returned v, Converges.of_succ (max (Nc + 1) (N₁ + 1)) fun m hm => ?_, ?_⟩
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          simp [execStmts, execStmt, TStmts.erase, hc m' (by omega), h₁ m' (by omega), hcv, Ty.encode,
            bind, Except.bind, pure, Except.pure]
        · simpa [StmtsRel, TStmts.denote, hcv] using rel₁
      | normal env =>
        obtain ⟨hret, bs, ρ', rfl, hk⟩ := rel₁
        obtain ⟨out₂, ⟨N₂, h₂⟩, rel₂⟩ := TStmts.adequate rest k ρ'
        refine ⟨out₂, Converges.of_succ (max (Nc + 1) (max (N₁ + 1) N₂)) fun m hm => ?_, ?_⟩
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          simp [execStmts, execStmt, TStmts.erase, hc m' (by omega), h₁ m' (by omega), hcv, Ty.encode,
            restore_toEnv, h₂ (m' + 1) (by omega), bind, Except.bind, pure, Except.pure]
        · have hd : (TStmts.ite c yes no rest).denote fs k ρ = rest.denote fs k ρ' := by
            simp [TStmts.denote, hcv, hk]
          rw [hd]
          cases out₂ with
          | returned v => exact rel₂
          | normal env => exact ⟨by simp [TStmts.returns, hret, rel₂.1], rel₂.2⟩
    | false =>
      obtain ⟨out₁, ⟨N₁, h₁⟩, rel₁⟩ := TStmts.adequate no (rest.denote fs k) ρ
      cases out₁ with
      | returned v =>
        refine ⟨.returned v, Converges.of_succ (max (Nc + 1) (N₁ + 1)) fun m hm => ?_, ?_⟩
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          simp [execStmts, execStmt, TStmts.erase, hc m' (by omega), h₁ m' (by omega), hcv, Ty.encode,
            bind, Except.bind, pure, Except.pure]
        · simpa [StmtsRel, TStmts.denote, hcv] using rel₁
      | normal env =>
        obtain ⟨hret, bs, ρ', rfl, hk⟩ := rel₁
        obtain ⟨out₂, ⟨N₂, h₂⟩, rel₂⟩ := TStmts.adequate rest k ρ'
        refine ⟨out₂, Converges.of_succ (max (Nc + 1) (max (N₁ + 1) N₂)) fun m hm => ?_, ?_⟩
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          simp [execStmts, execStmt, TStmts.erase, hc m' (by omega), h₁ m' (by omega), hcv, Ty.encode,
            restore_toEnv, h₂ (m' + 1) (by omega), bind, Except.bind, pure, Except.pure]
        · have hd : (TStmts.ite c yes no rest).denote fs k ρ = rest.denote fs k ρ' := by
            simp [TStmts.denote, hcv, hk]
          rw [hd]
          cases out₂ with
          | returned v => exact rel₂
          | normal env => exact ⟨by simp [TStmts.returns, hret, rel₂.1], rel₂.2⟩

end

/-! ## Programs -/

/-- `prog` resolves each function of `P` to its erasure. -/
def Lookups (prog : Program) : TProgram Φ → Prop
  | .nil => True
  | .cons s body rest =>
    prog.find? (·.name == s.name) = some { name := s.name, params := s.params.map Prod.fst, body := body.erase } ∧
      Lookups prog rest

theorem TProgram.fnsOK {prog : Program} : ∀ {Φ : Sigs} (P : TProgram Φ), Lookups prog P → P.returns = true →
    FnsOK prog P.denote
  | _, .nil, _, _ => fun v => nomatch v
  | _, .cons s body rest, h, hret => by
    obtain ⟨hfind, hrest⟩ := h
    simp only [TProgram.returns, Bool.and_eq_true] at hret
    have ih : FnsOK prog rest.denote := rest.fnsOK hrest hret.2
    intro v xs
    cases v with
    | there v => exact ih v xs
    | here =>
      obtain ⟨out, ⟨N, h⟩, rel⟩ := TStmts.adequate ih body (fun _ => Ty.default _) xs
      cases out with
      | normal env => simp [StmtsRel, hret.1] at rel
      | returned v =>
        refine Converges.of_succ N fun m hm => ?_
        have h := h m hm
        rw [← Ctx.zip_encode] at h
        simp [call, hfind, Ctx.encode_length, h, bind, Except.bind, pure, Except.pure]
        exact rel

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

/-! ## The theorem -/

/-- **Adequacy.** In a well-formed typed program, every function, run by the model
on the encoding of any arguments, converges to the encoding of its denotation. -/
theorem adequacy {Φ : Sigs} (P : TProgram Φ) (wf : P.WF) {f : String} {s : Sig} (v : FVar Φ f s)
    (xs : s.params.denote) :
    Converges (fun n => call P.erase n f (s.params.encode xs)) (.ok (s.result.encode (v.get P.denote xs))) :=
  P.fnsOK (P.lookups wf.1) wf.2 v xs

end V2
