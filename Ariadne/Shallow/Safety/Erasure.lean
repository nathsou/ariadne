import Ariadne.Shallow.Safety

namespace Ariadne.Shallow.Safety
open Core

inductive ListRelated (relation : α → β → Prop) : List α → List β → Prop where
  | nil : ListRelated relation [] []
  | cons : relation x y → ListRelated relation xs ys → ListRelated relation (x :: xs) (y :: ys)

theorem ListRelated.length {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) : a.length = b.length := by
  induction related <;> simp_all

theorem ListRelated.append {relation : α → β → Prop} {a c : List α} {b d : List β}
    (left : ListRelated relation a b) (right : ListRelated relation c d) :
    ListRelated relation (a ++ c) (b ++ d) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

theorem ListRelated.reverse {relation : α → β → Prop} {a : List α} {b : List β}
    (related : ListRelated relation a b) : ListRelated relation a.reverse b.reverse := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => simpa only [List.reverse_cons] using ih.append (.cons head .nil)

theorem ListRelated.map {relation : α → β → Prop} {result : γ → δ → Prop}
    {a : List α} {b : List β} (related : ListRelated relation a b) (f : α → γ) (g : β → δ)
    (step : ∀ x y, relation x y → result (f x) (g y)) : ListRelated result (a.map f) (b.map g) := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (step _ _ head) ih

theorem ListRelated.refl (a : List α) : ListRelated Eq a a := by
  induction a with
  | nil => exact .nil
  | cons x xs ih => exact .cons rfl ih

theorem ListRelated.eq {a b : List α} (related : ListRelated Eq a b) : a = b := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp [head, ih]

def OptionRelated (relation : α → β → Prop) (a : Option α) (b : Option β) : Prop :=
  match a, b with
  | none, none => True
  | some a, some b => relation a b
  | _, _ => False

theorem OptionRelated.isSome {relation : α → β → Prop} {a : Option α} {b : Option β}
    (related : OptionRelated relation a b) : a.isSome = b.isSome := by
  cases a <;> cases b <;> simp_all [OptionRelated]

/-- Guarded and native functions are related by their values on related inputs.
Container relations retain higher-order values rather than replacing callbacks
with functions that forget their guards. -/
def Erases {interp : Named.Interp} : (t : Core.Ty) → Model t interp → t.denote interp → Prop
  | .unit, a, b => a = b
  | .bool, a, b => a = b
  | .int, a, b => a = b
  | .int53, a, b => a = b
  | .number, a, b => a = b
  | .string, a, b => a = b
  | .named _, a, b => a = b
  | .option t, a, b => OptionRelated (Erases t) a b
  | .list t, a, b => ListRelated (Erases t) a b
  | .map k v, a, b => match k with
    | .number | .int | .int53 | .string | .bool =>
      ListRelated (fun a b => a.1 = b.1 ∧ Erases v a.2 b.2) a.entries b.entries
  | .set _, a, b => a = b
  | .pair a b, x, y => Erases a x.1 y.1 ∧ Erases b x.2 y.2
  | .sum a b, x, y => match x, y with
    | .inl x, .inl y => Erases a x y
    | .inr x, .inr y => Erases b x y
    | _, _ => False
  | .fn a b, f, g => ∀ x y, Erases a x y → Erases b (f x).1 (g y)
  | .step s r, x, y => match x, y with
    | .next x, .next y | .stop x, .stop y => Erases s x y
    | .ret x, .ret y => Erases r x y
    | _, _ => False
  | .exit s r, x, y => match x, y with
    | .done x, .done y => Erases s x y
    | .ret x, .ret y => Erases r x y
    | _, _ => False

theorem Erases.key (k : Key) (interp : Named.Interp)
    (a : Model k.type interp) (b : k.type.denote interp) :
    Erases k.type a b ↔ a = cast (by cases k <;> rfl : k.type.denote interp = Model k.type interp) b := by
  cases k <;> rfl

private theorem entries_get [eqκ : BEq κ] {left : List (κ × α)} {right : List (κ × β)}
    {relation : α → β → Prop} (related : ListRelated (fun a b => a.1 = b.1 ∧ relation a.2 b.2) left right)
    (key : κ) :
    OptionRelated relation (MapEntries.get left key) (MapEntries.get right key) := by
  induction related with
  | nil => trivial
  | @cons a b left right head tail ih =>
    rcases a with ⟨ka, va⟩; rcases b with ⟨kb, vb⟩
    rcases head with ⟨rfl, values⟩
    by_cases found : (ka == key) = true
    · simpa [MapEntries.get, found, OptionRelated] using values
    · simpa [MapEntries.get, found] using ih

theorem unary_erases {interp : Named.Interp} (op : Unary a b) (x : Model a interp) (y : a.denote interp)
    (related : Erases a x y) : Erases b (unary op x) (Denote.unary op y) := by
  cases op
  all_goals first | (solve | simp only [Erases] at related; cases related; rfl) | skip
  case isSome t =>
    cases x <;> cases y <;> simp_all [Erases, OptionRelated, unary, Denote.unary]
  case lengthInt53 t => exact congrArg Int.ofNat related.length
  case length t => exact congrArg Float.Model.ofNat related.length
  case reverse t => exact related.reverse
  case mapSizeInt53 k v =>
    cases k <;> exact congrArg Int.ofNat related.length
  case mapSize k v =>
    cases k <;> exact congrArg Float.Model.ofNat related.length
  case mapKeys k v =>
    cases k <;> exact related.map Prod.fst Prod.fst (fun _ _ h => h.1)
  case mapValues k v =>
    cases k <;> exact related.map Prod.snd Prod.snd (fun _ _ h => h.2)
  case mapEntries k v =>
    cases k <;> exact related
  case setValues k =>
    cases k <;> simp only [Erases] at related ⊢ <;> cases related <;> exact ListRelated.refl _
  case setEntries k =>
    cases k <;> simp only [Erases] at related ⊢ <;> cases related
    all_goals exact (ListRelated.refl _).map (fun a => (a,a)) (fun a => (a,a)) (fun _ _ h => ⟨h,h⟩)

private theorem list_get {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRelated relation left right) (index : Nat) :
    OptionRelated relation left[index]? right[index]? := by
  induction related generalizing index with
  | nil => trivial
  | cons head tail ih =>
    cases index with
    | zero => exact head
    | succ index => exact ih index

private theorem entries_set [BEq κ] {left : List (κ × α)} {right : List (κ × β)}
    {relation : α → β → Prop} (related : ListRelated (fun a b => a.1 = b.1 ∧ relation a.2 b.2) left right)
    (key : κ) {a : α} {b : β} (value : relation a b) :
    ListRelated (fun a b => a.1 = b.1 ∧ relation a.2 b.2)
      (MapEntries.set left key a) (MapEntries.set right key b) := by
  induction related with
  | nil => exact .cons ⟨rfl, value⟩ .nil
  | @cons a b left right head tail ih =>
    rcases a with ⟨ka, va⟩; rcases b with ⟨kb, vb⟩
    rcases head with ⟨rfl, values⟩
    by_cases found : (ka == key) = true
    · simpa [MapEntries.set, found] using ListRelated.cons ⟨rfl, value⟩ tail
    · simpa [MapEntries.set, found] using ListRelated.cons ⟨rfl, values⟩ ih

private theorem entries_delete [eqκ : BEq κ] {left : List (κ × α)} {right : List (κ × β)}
    {relation : α → β → Prop} (related : ListRelated (fun a b => a.1 = b.1 ∧ relation a.2 b.2) left right)
    (key : κ) :
    ListRelated (fun a b => a.1 = b.1 ∧ relation a.2 b.2)
      (MapEntries.delete left key) (MapEntries.delete right key) := by
  induction related with
  | nil => exact .nil
  | @cons a b left right head tail ih =>
    rcases a with ⟨ka, va⟩; rcases b with ⟨kb, vb⟩
    rcases head with ⟨rfl, values⟩
    by_cases found : (ka == key) = true
    · simpa [MapEntries.delete, found] using ih
    · simpa [MapEntries.delete, found] using ListRelated.cons ⟨rfl, values⟩ ih

theorem binary_erases {interp : Named.Interp} (op : Binary a b c)
    (x : Model a interp) (x' : a.denote interp) (y : Model b interp) (y' : b.denote interp)
    (left : Erases a x x') (right : Erases b y y') :
    Erases c (binary op x y) (Denote.binary op x' y') := by
  cases op
  all_goals first | (solve | simp only [Erases] at left right; cases left; cases right; rfl) | skip
  case guard => exact right
  case intRange =>
    simp only [Erases] at left right; cases left; cases right
    exact ListRelated.refl _
  case int53Range =>
    simp only [Erases] at left right; cases left; cases right
    exact ListRelated.refl _
  case append t => exact left.append right
  case get t =>
    simp only [Erases] at right
    cases right
    simp only [binary, Denote.binary, JSArray.get]
    cases indexOf (.number y) with
    | none => trivial
    | some index => simpa only [Option.bind_some, Erases] using list_get left index
  case mapGet k v =>
    cases k <;> simp only [Erases] at left right ⊢ <;> cases right
    all_goals
      simp only [binary, Denote.binary, JSMap.get, NumberMap.get]
      first | exact entries_get (eqκ := NumberKey.equality) left y | exact entries_get left y
  case mapHas k v =>
    cases k <;> simp only [Erases] at left right ⊢ <;> cases right
    all_goals
      simp only [binary, Denote.binary, JSMap.has, JSMap.get, NumberMap.has, NumberMap.get]
      first
      | exact (entries_get (eqκ := NumberKey.equality) left y).isSome
      | exact (entries_get left y).isSome
  case mapDelete k v =>
    cases k <;> simp only [Erases] at left right ⊢ <;> cases right
    all_goals
      simp only [binary, Denote.binary, JSMap.delete, NumberMap.delete, NumberMap.entries]
      first | exact entries_delete (eqκ := NumberKey.equality) left y | exact entries_delete left y
  case setHas k => cases k <;> simp only [Erases] at left right ⊢ <;> cases left <;> cases right <;> rfl
  case setAdd k => cases k <;> simp only [Erases] at left right ⊢ <;> cases left <;> cases right <;> rfl
  case setDelete k => cases k <;> simp only [Erases] at left right ⊢ <;> cases left <;> cases right <;> rfl

def ErasesEnvironment {interp : Named.Interp} (model : Environment Γ interp) (native : Core.Env Γ interp) : Prop :=
  ∀ {t} (v : Var Γ t), Erases t (getVariable v model) (v.get native)

theorem ErasesEnvironment.cons {interp : Named.Interp} {model : Environment Γ interp} {native : Core.Env Γ interp}
    (related : ErasesEnvironment model native) {value : Model t interp} {expected : t.denote interp}
    (equal : Erases t value expected) : ErasesEnvironment (Γ := t :: Γ) (interp := interp) (value, model) (expected, native) := by
  intro u v
  cases v with
  | here => exact equal
  | there v => exact related v

/-- Structural Core terms whose values erase compositionally. Collection
callbacks and named construction require their own traversal/layout lemmas. -/
inductive ErasureTerm : {Γ : List Core.Ty} → {t : Core.Ty} → Term Γ t → Prop where
  | var (v : Var Γ t) : ErasureTerm (.var v)
  | unit : ErasureTerm (.unit : Term Γ .unit)
  | bool (value : Bool) : ErasureTerm (.bool value : Term Γ .bool)
  | int (value : Int) : ErasureTerm (.int value : Term Γ .int)
  | number (mantissa : Nat) (exponent : Int) : ErasureTerm (.number mantissa exponent : Term Γ .number)
  | string (value : JSString) : ErasureTerm (.string value : Term Γ .string)
  | unary (op : Unary a b) {value : Term Γ a} (input : ErasureTerm value) : ErasureTerm (.unary op value)
  | binary (op : Binary a b c) {a : Term Γ a} {b : Term Γ b}
      (left : ErasureTerm a) (right : ErasureTerm b) : ErasureTerm (.binary op a b)
  | let_ (name : String) {value : Term Γ a} {body : Term (a :: Γ) b}
      (input : ErasureTerm value) (next : ErasureTerm body) : ErasureTerm (.let_ name value body)
  | ite {condition : Term Γ .bool} {yes no : Term Γ t}
      (test : ErasureTerm condition) (yesBody : ErasureTerm yes) (noBody : ErasureTerm no) :
      ErasureTerm (.ite condition yes no)
  | none : ErasureTerm (.none : Term Γ (.option t))
  | some {value : Term Γ t} (input : ErasureTerm value) : ErasureTerm (.some value)
  | optionCase {option : Term Γ (.option a)} {fallback : Term Γ b} {body : Term (a :: Γ) b}
      (input : ErasureTerm option) (empty : ErasureTerm fallback) (present : ErasureTerm body) :
      ErasureTerm (.optionCase option fallback body)
  | nil : ErasureTerm (.nil : Term Γ (.list t))
  | cons {value : Term Γ t} {rest : Term Γ (.list t)} (head : ErasureTerm value) (tail : ErasureTerm rest) :
      ErasureTerm (.cons value rest)
  | pair {a : Term Γ a} {b : Term Γ b} (left : ErasureTerm a) (right : ErasureTerm b) : ErasureTerm (.pair a b)
  | fst {value : Term Γ (.pair a b)} (input : ErasureTerm value) : ErasureTerm (.fst value)
  | snd {value : Term Γ (.pair a b)} (input : ErasureTerm value) : ErasureTerm (.snd value)
  | inl {value : Term Γ a} (input : ErasureTerm value) : ErasureTerm (.inl (b := b) value)
  | inr {value : Term Γ b} (input : ErasureTerm value) : ErasureTerm (.inr (a := a) value)
  | sumCase {value : Term Γ (.sum a b)} {left : Term (a :: Γ) c} {right : Term (b :: Γ) c}
      (input : ErasureTerm value) (lhs : ErasureTerm left) (rhs : ErasureTerm right) :
      ErasureTerm (.sumCase value left right)
  | lam (name : String) {body : Term (a :: Γ) b} (input : ErasureTerm body) : ErasureTerm (.lam name body)
  | app {f : Term Γ (.fn a b)} {arg : Term Γ a} (function : ErasureTerm f) (argument : ErasureTerm arg) :
      ErasureTerm (.app f arg)
  | closed {body : Term [] t} (input : ErasureTerm body) : ErasureTerm (Term.closed (Γ := Γ) body)

/-- Function guards are retained in the model, while all related results agree
with native evaluation. This lemma does not assert operational source adequacy. -/
theorem ErasureTerm.value {interp : Named.Interp} {body : Term Γ t} (input : ErasureTerm body)
    (model : Environment Γ interp) (native : Core.Env Γ interp) (related : ErasesEnvironment model native) :
    Erases t (term body model).1 (Denote.term body native) := by
  induction input with
  | var v => exact related v
  | unit => rfl
  | bool value => rfl
  | int value => rfl
  | number mantissa exponent => rfl
  | string value => rfl
  | unary op input ih => exact unary_erases op _ _ (ih model native related)
  | binary op left right ihl ihr => exact binary_erases op _ _ _ _ (ihl model native related) (ihr model native related)
  | let_ name input next ihv ihb => exact ihb _ _ (related.cons (ihv model native related))
  | @ite Γ t condition yes no test yesBody noBody ihc ihy ihn =>
    have testValue : (term condition model).1 = Denote.term condition native := ihc model native related
    cases value : Denote.term condition native
    · simpa only [term, testValue, Denote.term, value, Bool.false_eq_true, ↓reduceIte] using ihn model native related
    · simpa only [term, testValue, Denote.term, value, ↓reduceIte] using ihy model native related
  | none => trivial
  | some input ih => exact ih model native related
  | @optionCase Γ a b option fallback body input empty present iho ihe ihp =>
    have options := iho model native related
    cases hx : (term option model).1 <;> cases hy : Denote.term option native
    all_goals simp only [hx, hy, Erases, OptionRelated] at options
    · simpa only [term, Denote.term, hx, hy, Option.elim_none] using ihe model native related
    · simpa only [term, Denote.term, hx, hy, Option.elim_some] using ihp _ _ (related.cons options)
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons (ihh model native related) (iht model native related)
  | pair left right ihl ihr => exact ⟨ihl model native related, ihr model native related⟩
  | fst input ih => exact (ih model native related).1
  | snd input ih => exact (ih model native related).2
  | inl input ih => exact ih model native related
  | inr input ih => exact ih model native related
  | @sumCase Γ a b c value left right input lhs rhs ihv ihl ihr =>
    have values := ihv model native related
    cases hx : (term value model).1 <;> cases hy : Denote.term value native
    all_goals simp only [hx, hy, Erases] at values
    · simpa only [term, Denote.term, hx, hy, Sum.elim_inl] using ihl _ _ (related.cons values)
    · simpa only [term, Denote.term, hx, hy, Sum.elim_inr] using ihr _ _ (related.cons values)
  | lam name input ih =>
    intro x y h
    exact ih _ _ (related.cons h)
  | app function argument ihf iha => exact ihf model native related _ _ (iha model native related)
  | closed input ih => exact ih () () (by intro t v; cases v)

theorem ErasureTerm.rename {body : Term Γ t} (input : ErasureTerm body) (r : Renaming Γ Δ) :
    ErasureTerm (body.rename r) := by
  induction input generalizing Δ with
  | var v => exact .var _
  | unit => exact .unit
  | bool value => exact .bool _
  | int value => exact .int _
  | number mantissa exponent => exact .number _ _
  | string value => exact .string _
  | unary op input ih => exact .unary op (ih r)
  | binary op left right ihl ihr => exact .binary op (ihl r) (ihr r)
  | let_ name input next ihv ihb => exact .let_ name (ihv r) (ihb r.lift)
  | ite test yes no ihc ihy ihn => exact .ite (ihc r) (ihy r) (ihn r)
  | none => exact .none
  | some input ih => exact .some (ih r)
  | optionCase input empty present iho ihe ihp => exact .optionCase (iho r) (ihe r) (ihp r.lift)
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons (ihh r) (iht r)
  | pair left right ihl ihr => exact .pair (ihl r) (ihr r)
  | fst input ih => exact .fst (ih r)
  | snd input ih => exact .snd (ih r)
  | inl input ih => exact .inl (ih r)
  | inr input ih => exact .inr (ih r)
  | sumCase input lhs rhs ihv ihl ihr => exact .sumCase (ihv r) (ihl r.lift) (ihr r.lift)
  | lam name input ih => exact .lam name (ih r.lift)
  | app function argument ihf iha => exact .app (ihf r) (iha r)
  | closed input ih => exact .closed input

private theorem erasure_lift {a : Core.Ty} (s : Substitution Γ Δ)
    (variables : ∀ {t} (v : Var Γ t), ErasureTerm (s v)) :
    ∀ {t} (v : Var (a :: Γ) t), ErasureTerm (s.lift v) := by
  intro t v
  cases v with
  | here => exact .var _
  | there v => exact (variables v).rename (fun v => .there v)

theorem ErasureTerm.substitute {body : Term Γ t} (input : ErasureTerm body) (s : Substitution Γ Δ)
    (variables : ∀ {t} (v : Var Γ t), ErasureTerm (s v)) : ErasureTerm (body.substitute s) := by
  induction input generalizing Δ with
  | var v => exact variables v
  | unit => exact .unit
  | bool value => exact .bool _
  | int value => exact .int _
  | number mantissa exponent => exact .number _ _
  | string value => exact .string _
  | unary op input ih => exact .unary op (ih s variables)
  | binary op left right ihl ihr => exact .binary op (ihl s variables) (ihr s variables)
  | let_ name input next ihv ihb => exact .let_ name (ihv s variables) (ihb s.lift (erasure_lift s variables))
  | ite test yes no ihc ihy ihn => exact .ite (ihc s variables) (ihy s variables) (ihn s variables)
  | none => exact .none
  | some input ih => exact .some (ih s variables)
  | optionCase input empty present iho ihe ihp => exact .optionCase (iho s variables) (ihe s variables) (ihp s.lift (erasure_lift s variables))
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons (ihh s variables) (iht s variables)
  | pair left right ihl ihr => exact .pair (ihl s variables) (ihr s variables)
  | fst input ih => exact .fst (ih s variables)
  | snd input ih => exact .snd (ih s variables)
  | inl input ih => exact .inl (ih s variables)
  | inr input ih => exact .inr (ih s variables)
  | sumCase input lhs rhs ihv ihl ihr => exact .sumCase (ihv s variables) (ihl s.lift (erasure_lift s variables)) (ihr s.lift (erasure_lift s variables))
  | lam name input ih => exact .lam name (ih s.lift (erasure_lift s variables))
  | app function argument ihf iha => exact .app (ihf s variables) (iha s variables)
  | closed input ih => exact .closed input

theorem ErasureTerm.project {tuple : Term Δ (environmentType Γ)} (input : ErasureTerm tuple) (v : Var Γ t) :
    ErasureTerm (Core.project tuple v) := by
  induction v generalizing Δ with
  | here => exact .fst input
  | there v ih => exact ih (.snd input)

theorem ErasureTerm.abstract {body : Term Γ t} (input : ErasureTerm body) :
    ErasureTerm (body.abstract : Term Δ (.fn (environmentType Γ) t)) :=
  .closed (.lam "state" (input.substitute _ (fun v => ErasureTerm.project (.var .here) v)))

end Ariadne.Shallow.Safety
