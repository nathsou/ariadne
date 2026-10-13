import V2.Proof.Basic

/-!
# Numbers, arrays and callbacks

Facts about the model's safe-integer check, array operations, and the array
methods that apply a callback element by element.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace V2

theorem inRange_iff {n : Int} : inRange n = true ↔ -maxSafe ≤ n ∧ n ≤ maxSafe := by
  simp only [inRange, Nat.ble_eq, maxSafe]
  cases n <;> simp <;> omega

theorem number_ok {n : Int} (h : inRange n = true) : number n = .ok (.number n) := by
  simp [number, inRange_iff.mp h]

/-! ## Lists related elementwise -/

theorem Forall2.length_eq {R : α → β → Prop} : ∀ {as bs}, Forall2 R as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length_eq]

theorem Forall2.append {R : α → β → Prop} : ∀ {as bs cs ds}, Forall2 R as bs → Forall2 R cs ds →
    Forall2 R (as ++ cs) (bs ++ ds)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons r h, h' => .cons r (h.append h')

theorem Forall2.getElem? {R : α → β → Prop} : ∀ {as bs}, Forall2 R as bs → ∀ i : Nat,
    (as[i]? = none ∧ bs[i]? = none) ∨ ∃ a b, as[i]? = some a ∧ bs[i]? = some b ∧ R a b
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons r _, 0 => .inr ⟨_, _, rfl, rfl, r⟩
  | _, _, .cons _ h, i + 1 => by simpa using h.getElem? i

theorem Forall2.filterMap_idx {R : α → β → Prop} {as bs} (h : Forall2 R as bs) :
    ∀ is : List Nat, Forall2 R (is.filterMap (as[·]?)) (is.filterMap (bs[·]?))
  | [] => .nil
  | i :: is => by
    rcases h.getElem? i with ⟨h1, h2⟩ | ⟨a, b, h1, h2, r⟩
    · simpa [List.filterMap_cons, h1, h2] using h.filterMap_idx is
    · simpa [List.filterMap_cons, h1, h2] using Forall2.cons r (h.filterMap_idx is)

theorem Forall2.map_left {R : α → β → Prop} {S : γ → β → Prop} {f : α → γ} (hf : ∀ a b, R a b → S (f a) b) :
    ∀ {as bs}, Forall2 R as bs → Forall2 S (as.map f) bs
  | _, _, .nil => .nil
  | _, _, .cons r h => .cons (hf _ _ r) (h.map_left hf)

/-- The iterations of `entries()`: each element with its index. -/
theorem Forall2.zipIdx {R : α → β → Prop} : ∀ {as bs} (s : Nat), Forall2 R as bs →
    Forall2 (fun (a : α × Nat) (b : β × Nat) => R a.1 b.1 ∧ a.2 = b.2) (as.zipIdx s) (bs.zipIdx s)
  | _, _, _, .nil => .nil
  | _, _, s, .cons r h => by simpa [List.zipIdx_cons] using Forall2.cons ⟨r, rfl⟩ (h.zipIdx (s + 1))

theorem index_rep {τ : Ty} {vs : List JSValue} {xs : List τ.denote} (h : Forall2 (fun w x => τ.Rep w x) vs xs)
    (i : Int) :
    (Ty.option .undef τ).Rep (if 0 ≤ i then (vs[i.toNat]?).getD .undefined else .undefined) (listIndex xs i) := by
  unfold listIndex
  split
  · rcases h.getElem? i.toNat with ⟨h1, h2⟩ | ⟨a, b, h1, h2, r⟩
    · simp only [h1, h2, Option.getD_none, Ty.Rep, Nullish.admits]
    · simpa only [h1, h2, Option.getD_some, Ty.Rep] using r
  · simp only [Ty.Rep, Nullish.admits]

theorem includes_rep {τ : Ty} (hp : τ.prim = true) {wx : JSValue} {x : τ.denote} (hx : τ.Rep wx x) :
    ∀ {vs : List JSValue} {xs : List τ.denote}, Forall2 (fun w y => τ.Rep w y) vs xs →
      includes wx vs = .ok (xs.any fun y => τ.beq y x)
  | _, _, .nil => rfl
  | _, _, .cons hw rest => by
    simp only [includes, Ty.strictEq_rep hp hw hx, bind, Except.bind, List.any_cons]
    cases τ.beq _ x <;> simp [includes_rep hp hx rest, pure, Except.pure]

theorem sortedBy_rep {τ : Ty} {vs : List JSValue} {xs : List τ.denote} (h : Forall2 (fun w x => τ.Rep w x) vs xs)
    (cmp : τ.denote → τ.denote → Int) :
    Forall2 (fun w x => τ.Rep w x) ((sortIndices (signs cmp xs) vs.length).filterMap (vs[·]?)) (sortedBy cmp xs) := by
  rw [h.length_eq]; exact h.filterMap_idx _

/-! ## Callbacks -/

section
variable {prog : Program}

theorem conv_arrow {env : Env} {ps : List String} {body : Expr} :
    Converges (fun n => evalArgs prog n env [.arrow ps body]) (.ok [.closure ps body env]) :=
  Converges.of_succ 1 fun m hm => by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp [evalArgs, evalExpr, bind, Except.bind, pure, Except.pure]

theorem apply_closure1 {x : String} {body : Expr} {cenv : Env} {w : JSValue} {r : Except Fault JSValue}
    (extra : List JSValue) (h : Converges (fun n => evalExpr prog n ((x, w) :: cenv) body) r) :
    Converges (fun n => apply prog n (.closure [x] body cenv) (w :: extra)) r := by
  obtain ⟨N, h⟩ := h
  exact Converges.of_succ N fun m hm => by simp [apply, bindParams, h m hm]

theorem apply_closure2 {x y : String} {body : Expr} {cenv : Env} {w₁ w₂ : JSValue} {r : Except Fault JSValue}
    (h : Converges (fun n => evalExpr prog n ((x, w₁) :: (y, w₂) :: cenv) body) r) :
    Converges (fun n => apply prog n (.closure [x, y] body cenv) [w₁, w₂]) r := by
  obtain ⟨N, h⟩ := h
  exact Converges.of_succ N fun m hm => by simp [apply, bindParams, h m hm]

variable {τ : Ty} {f arr : JSValue}

/-- The callback, applied to an element, converges to a Boolean. -/
abbrev PredOK (prog : Program) (τ : Ty) (f arr : JSValue) (P S : τ.denote → Bool) : Prop :=
  ∀ (i : Nat) w a, τ.Rep w a → S a = true → Converges (fun n => apply prog n f [w, .number i, arr]) (.ok (.bool (P a)))

theorem PredOK.of {P S : τ.denote → Bool}
    (h : ∀ (extra : List JSValue) w y, τ.Rep w y → S y = true →
      ∃ r, Converges (fun n => apply prog n f (w :: extra)) (.ok r) ∧ Ty.bool.Rep r (P y)) :
    PredOK prog τ f arr P S := fun i w y hw hs => by
  obtain ⟨r, hc, hr⟩ := h _ w y hw hs
  simp only [Ty.Rep] at hr; subst hr; exact hc

theorem someApply_conv {P S : τ.denote → Bool} (happ : PredOK prog τ f arr P S) :
    ∀ {vs : List JSValue} {xs : List τ.denote} (i : Nat), Forall2 (fun w x => τ.Rep w x) vs xs →
      anySafe P S xs = true → Converges (fun n => someApply prog n f vs i arr) (.ok (xs.any P))
  | _, _, _, .nil, _ => Converges.of_succ 0 fun m _ => by simp [someApply]
  | w :: _, a :: _, i, .cons hw rest, hs => by
    simp only [anySafe, Bool.and_eq_true, Bool.or_eq_true] at hs
    obtain ⟨Na, ha⟩ := happ i _ _ hw hs.1
    cases hp : P a
    · obtain ⟨Nr, hr⟩ := someApply_conv happ (i + 1) rest (by simpa [hp] using hs.2)
      exact Converges.of_succ (max Na Nr) fun m hm => by
        simp [someApply, ha m (by omega), hr m (by omega), hp, bind, Except.bind]
    · exact Converges.of_succ Na fun m hm => by simp [someApply, ha m hm, hp, bind, Except.bind]

theorem everyApply_conv {P S : τ.denote → Bool} (happ : PredOK prog τ f arr P S) :
    ∀ {vs : List JSValue} {xs : List τ.denote} (i : Nat), Forall2 (fun w x => τ.Rep w x) vs xs →
      allSafe P S xs = true → Converges (fun n => everyApply prog n f vs i arr) (.ok (xs.all P))
  | _, _, _, .nil, _ => Converges.of_succ 0 fun m _ => by simp [everyApply]
  | w :: _, a :: _, i, .cons hw rest, hs => by
    simp only [allSafe, Bool.and_eq_true, Bool.or_eq_true] at hs
    obtain ⟨Na, ha⟩ := happ i _ _ hw hs.1
    cases hp : P a
    · exact Converges.of_succ Na fun m hm => by simp [everyApply, ha m hm, hp, bind, Except.bind]
    · obtain ⟨Nr, hr⟩ := everyApply_conv happ (i + 1) rest (by simpa [hp] using hs.2)
      exact Converges.of_succ (max Na Nr) fun m hm => by
        simp [everyApply, ha m (by omega), hr m (by omega), hp, bind, Except.bind]

theorem findApply_conv {P S : τ.denote → Bool} (happ : PredOK prog τ f arr P S) :
    ∀ {vs : List JSValue} {xs : List τ.denote} (i : Nat), Forall2 (fun w x => τ.Rep w x) vs xs →
      anySafe P S xs = true →
      ∃ r, Converges (fun n => findApply prog n f vs i arr) (.ok r) ∧ (Ty.option .undef τ).Rep r (xs.find? P)
  | _, _, _, .nil, _ => ⟨.undefined, Converges.of_succ 0 fun m _ => by simp [findApply], rfl⟩
  | w :: _, a :: _, i, .cons hw rest, hs => by
    simp only [anySafe, Bool.and_eq_true, Bool.or_eq_true] at hs
    obtain ⟨Na, ha⟩ := happ i _ _ hw hs.1
    cases hp : P a
    · obtain ⟨r, ⟨Nr, hr⟩, hrep⟩ := findApply_conv happ (i + 1) rest (by simpa [hp] using hs.2)
      exact ⟨r, Converges.of_succ (max Na Nr) fun m hm => by
        simp [findApply, ha m (by omega), hr m (by omega), hp, bind, Except.bind], by simpa [hp] using hrep⟩
    · exact ⟨w, Converges.of_succ Na fun m hm => by simp [findApply, ha m hm, hp, bind, Except.bind],
        by simpa [hp, Ty.Rep] using hw⟩

theorem filterApply_conv {P S : τ.denote → Bool} (happ : PredOK prog τ f arr P S) :
    ∀ {vs : List JSValue} {xs : List τ.denote} (i : Nat), Forall2 (fun w x => τ.Rep w x) vs xs →
      xs.all S = true →
      ∃ rs, Converges (fun n => filterApply prog n f vs i arr) (.ok rs) ∧ Forall2 (fun w x => τ.Rep w x) rs (xs.filter P)
  | _, _, _, .nil, _ => ⟨[], Converges.of_succ 0 fun m _ => by simp [filterApply], .nil⟩
  | w :: _, a :: _, i, .cons hw rest, hs => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    obtain ⟨Na, ha⟩ := happ i _ _ hw hs.1
    obtain ⟨rs, ⟨Nr, hr⟩, hrep⟩ := filterApply_conv happ (i + 1) rest hs.2
    cases hp : P a
    · exact ⟨rs, Converges.of_succ (max Na Nr) fun m hm => by
        simp [filterApply, ha m (by omega), hr m (by omega), hp, bind, Except.bind], by simpa [hp] using hrep⟩
    · exact ⟨w :: rs, Converges.of_succ (max Na Nr) fun m hm => by
        simp [filterApply, ha m (by omega), hr m (by omega), hp, bind, Except.bind, pure, Except.pure],
        by simpa [hp] using Forall2.cons hw hrep⟩

theorem mapApply_conv {σ : Ty} {F : τ.denote → σ.denote} {S : τ.denote → Bool}
    (happ : ∀ (i : Nat) w a, τ.Rep w a → S a = true →
      ∃ r, Converges (fun n => apply prog n f [w, .number i, arr]) (.ok r) ∧ σ.Rep r (F a)) :
    ∀ {vs : List JSValue} {xs : List τ.denote} (i : Nat), Forall2 (fun w x => τ.Rep w x) vs xs →
      xs.all S = true →
      ∃ rs, Converges (fun n => mapApply prog n f vs i arr) (.ok rs) ∧ Forall2 (fun w x => σ.Rep w x) rs (xs.map F)
  | _, _, _, .nil, _ => ⟨[], Converges.of_succ 0 fun m _ => by simp [mapApply], .nil⟩
  | w :: _, a :: _, i, .cons hw rest, hs => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    obtain ⟨r, ⟨Na, ha⟩, hr⟩ := happ i _ _ hw hs.1
    obtain ⟨rs, ⟨Nr, hrs⟩, hrep⟩ := mapApply_conv happ (i + 1) rest hs.2
    exact ⟨r :: rs, Converges.of_succ (max Na Nr) fun m hm => by
      simp [mapApply, ha m (by omega), hrs m (by omega), bind, Except.bind, pure, Except.pure], .cons hr hrep⟩

/-- The comparator, applied to two elements, converges to a number. -/
abbrev CmpOK (prog : Program) (τ : Ty) (f : JSValue) (C : τ.denote → τ.denote → Int)
    (S : τ.denote → τ.denote → Bool) : Prop :=
  ∀ w₁ a₁ w₂ a₂, τ.Rep w₁ a₁ → τ.Rep w₂ a₂ → S a₁ a₂ = true →
    Converges (fun n => apply prog n f [w₁, w₂]) (.ok (.number (C a₁ a₂)))

theorem compareRow_conv {C : τ.denote → τ.denote → Int} {S : τ.denote → τ.denote → Bool} (happ : CmpOK prog τ f C S)
    {w : JSValue} {a : τ.denote} (hw : τ.Rep w a) :
    ∀ {vs : List JSValue} {xs : List τ.denote}, Forall2 (fun w x => τ.Rep w x) vs xs → xs.all (S a) = true →
      Converges (fun n => compareRow prog n f w vs) (.ok (xs.map fun y => sign (C a y)))
  | _, _, .nil, _ => Converges.of_succ 0 fun m _ => by simp [compareRow]
  | _, _, .cons hy rest, hs => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    obtain ⟨Na, ha⟩ := happ _ _ _ _ hw hy hs.1
    obtain ⟨Nr, hr⟩ := compareRow_conv happ hw rest hs.2
    exact Converges.of_succ (max Na Nr) fun m hm => by
      simp [compareRow, ha m (by omega), hr m (by omega), bind, Except.bind, pure, Except.pure]

theorem compareAll_conv {C : τ.denote → τ.denote → Int} {S : τ.denote → τ.denote → Bool} (happ : CmpOK prog τ f C S)
    {ws : List JSValue} {ys : List τ.denote} (hys : Forall2 (fun w x => τ.Rep w x) ws ys) :
    ∀ {vs : List JSValue} {xs : List τ.denote}, Forall2 (fun w x => τ.Rep w x) vs xs →
      xs.all (fun x => ys.all (S x)) = true →
      Converges (fun n => compareAll prog n f vs ws) (.ok (xs.map fun x => ys.map fun y => sign (C x y)))
  | _, _, .nil, _ => Converges.of_succ 0 fun m _ => by simp [compareAll]
  | _, _, .cons hx rest, hs => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    obtain ⟨Na, ha⟩ := compareRow_conv happ hx hys hs.1
    obtain ⟨Nr, hr⟩ := compareAll_conv happ hys rest hs.2
    exact Converges.of_succ (max Na Nr) fun m hm => by
      simp [compareAll, ha m (by omega), hr m (by omega), bind, Except.bind, pure, Except.pure]

end

end V2
