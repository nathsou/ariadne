import V2.Proof.Array

/-!
# Maps and the object's state

The model's maps and the denotation's maps run the same operations (`mapGet`,
`mapPut`, `mapDel`) on related association lists; a method's state is the record
bound to `this`, and changing one of its maps replaces that field.
-/

set_option linter.unusedSimpArgs false

namespace V2

/-- Entries related key by key: the same key, and represented values. -/
def MapRel (τ : Ty) (p : JSString × JSValue) (q : JSString × τ.denote) : Prop := p.1 = q.1 ∧ τ.Rep p.2 q.2

theorem map_rep {τ : Ty} {w : JSValue} {m : List (JSString × τ.denote)} :
    (Ty.map τ).Rep w m ↔ ∃ kvs, w = .map kvs ∧ Forall2 (MapRel τ) kvs m := by
  simp only [Ty.Rep]; rfl

theorem mapGet_rep {τ : Ty} (k : JSString) : ∀ {kvs : List (JSString × JSValue)} {m : List (JSString × τ.denote)},
    Forall2 (MapRel τ) kvs m →
      (mapGet kvs k = none ∧ mapGet m k = none) ∨ ∃ w x, mapGet kvs k = some w ∧ mapGet m k = some x ∧ τ.Rep w x
  | [], [], .nil => .inl ⟨rfl, rfl⟩
  | (k', w) :: _, (k'', x) :: _, .cons ⟨hk, hw⟩ rest => by
    simp only at hk; subst hk
    by_cases h : k = k'
    · subst h; exact .inr ⟨w, x, by simp [mapGet, List.lookup], by simp [mapGet, List.lookup], hw⟩
    · have hne : (k == k') = false := beq_eq_false_iff_ne.mpr h
      simpa [mapGet, List.lookup, hne] using mapGet_rep k rest

theorem mapPut_rep {τ : Ty} (k : JSString) {w : JSValue} {x : τ.denote} (hw : τ.Rep w x) :
    ∀ {kvs : List (JSString × JSValue)} {m : List (JSString × τ.denote)},
    Forall2 (MapRel τ) kvs m → Forall2 (MapRel τ) (mapPut kvs k w) (mapPut m k x)
  | [], [], .nil => .cons ⟨rfl, hw⟩ .nil
  | (k', _) :: _, (k'', _) :: _, .cons ⟨hk, hv⟩ rest => by
    simp only at hk; subst hk
    by_cases h : k' = k
    · subst h; simp only [mapPut, beq_self_eq_true, ↓reduceIte]; exact .cons ⟨rfl, hw⟩ rest
    · have hne : (k' == k) = false := beq_eq_false_iff_ne.mpr h
      simp only [mapPut, hne, Bool.false_eq_true, ↓reduceIte]
      exact .cons ⟨rfl, hv⟩ (mapPut_rep k hw rest)

theorem mapDel_rep {τ : Ty} (k : JSString) : ∀ {kvs : List (JSString × JSValue)} {m : List (JSString × τ.denote)},
    Forall2 (MapRel τ) kvs m → Forall2 (MapRel τ) (mapDel kvs k) (mapDel m k)
  | [], [], .nil => .nil
  | (k', _) :: _, (k'', _) :: _, .cons ⟨hk, hv⟩ rest => by
    simp only at hk; subst hk
    have ih := mapDel_rep k rest
    unfold mapDel at ih ⊢
    by_cases h : k' = k
    · subst h; simpa using ih
    · have hne : (k' != k) = true := by simp [h]
      simp only [List.filter, hne]
      exact .cons ⟨rfl, hv⟩ ih

theorem keys_rep {τ : Ty} : ∀ {kvs : List (JSString × JSValue)} {m : List (JSString × τ.denote)},
    Forall2 (MapRel τ) kvs m → Forall2 (fun w x => Ty.string.Rep w x) (kvs.map (.string ·.1)) (m.map Prod.fst)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons ⟨hk, _⟩ rest => .cons (by simp [Ty.Rep, hk]) (keys_rep rest)

theorem values_rep {τ : Ty} : ∀ {kvs : List (JSString × JSValue)} {m : List (JSString × τ.denote)},
    Forall2 (MapRel τ) kvs m → Forall2 (fun w x => τ.Rep w x) (kvs.map (·.2)) (m.map Prod.snd)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons ⟨_, hv⟩ rest => .cons hv (values_rep rest)

theorem FIdx.mem_names : ∀ {fs : Fields} {f τ} (_ : FIdx fs f τ), f ∈ fs.names
  | .cons _ _ _, _, _, .here => by simp [Fields.names]
  | .cons _ _ _, _, _, .there i => by simp [Fields.names, i.mem_names]

/-- Replacing a field of a record with distinct field names. -/
theorem FIdx.rep_set : ∀ {fs : Fields} {f τ} (i : FIdx fs f τ) {kvs : List (String × JSValue)} {x : fs.denote}
    {w : JSValue} {y : τ.denote}, fs.names.Nodup → fs.Rep kvs x → τ.Rep w y → fs.Rep (upsert kvs f w) (i.set x y)
  | .cons _ _ rest, f, _, .here, kvs, (_, xs), w, y, nd, ⟨_, hr⟩, hw => by
    simp only [Fields.names, List.nodup_cons] at nd
    refine ⟨by simpa [fieldOf_upsert] using hw, Fields.rep_congr (fun g hg => ?_) hr⟩
    have : g ≠ f := fun h => nd.1 (by subst h; exact hg)
    simp [fieldOf_upsert, this]
  | .cons g _ rest, f, _, .there i, kvs, (x, xs), w, y, nd, ⟨hx, hr⟩, hw => by
    simp only [Fields.names, List.nodup_cons] at nd
    have hgf : g ≠ f := fun h => nd.1 (h ▸ i.mem_names)
    exact ⟨by simpa [fieldOf_upsert, hgf] using hx, i.rep_set nd.2 hr hw⟩

/-- `this.f`, a map field of the state: the model finds it. -/
theorem stateMap_rep {Γ : Ctx} {env : Env} {ρ : Γ.denote} {fs : Fields} {f : String} {τ : Ty}
    (v : Var Γ "this" (.record fs)) (i : FIdx fs f (.map τ)) (he : EnvRel Γ env ρ) :
    ∃ kvs, stateMap env f = .ok kvs ∧ Forall2 (MapRel τ) kvs (i.get (v.get ρ)) := by
  obtain ⟨w, hl, kvs0, rfl, _, hr⟩ := v.lookup he
  obtain ⟨kvs, hf, hm⟩ := map_rep.mp (i.rep hr)
  have : kvs0.lookup f = some (.map kvs) := by
    unfold fieldOf at hf
    cases h : kvs0.lookup f <;> simp_all
  exact ⟨kvs, by simp [stateMap, hl, this], hm⟩

/-- Replacing a map field of the state. -/
theorem setStateMap_rep {Γ : Ctx} {env : Env} {ρ : Γ.denote} {fs : Fields} {f : String} {τ : Ty}
    (v : Var Γ "this" (.record fs)) (i : FIdx fs f (.map τ)) (nd : fs.names.Nodup) (he : EnvRel Γ env ρ)
    {kvs : List (JSString × JSValue)} {m : List (JSString × τ.denote)} (hm : Forall2 (MapRel τ) kvs m) :
    ∃ env', setStateMap env f kvs = .ok env' ∧ env'.length = env.length ∧
      EnvRel Γ env' (v.set ρ (i.set (v.get ρ) m)) := by
  obtain ⟨w, hl, kvs0, rfl, hnd, hr⟩ := v.lookup he
  have hrep : (Ty.record fs).Rep (.record (upsert kvs0 f (.map kvs))) (i.set (v.get ρ) m) :=
    ⟨_, rfl, nodup_upsert _ _ _ hnd, i.rep_set nd hr (map_rep.mpr ⟨kvs, rfl, hm⟩)⟩
  obtain ⟨env', ha, hlen, hrel⟩ := v.assignRel he hrep
  exact ⟨env', by simp [setStateMap, hl, ha], hlen, hrel⟩

theorem thisOf_rep {Γ : Ctx} {env : Env} {ρ : Γ.denote} {σ : Ty} (v : Var Γ "this" σ) (he : EnvRel Γ env ρ) :
    ∃ w, thisOf env = .ok w ∧ σ.Rep w (v.get ρ) := by
  obtain ⟨w, hl, hw⟩ := v.lookup he
  exact ⟨w, by simp [thisOf, hl], hw⟩

end V2
