import V2.Typed.Syntax
import V2.Kernel

/-!
# Denotation and safety

Expressions denote functions of the environment tuple. Statement lists denote in
continuation-passing style: `ss.denote fs k ρ` is the function's result when the
list runs in `ρ`, and `k` gives the result of what follows when the list ends
normally, with `break`, or with `continue`. `return` discards `k`. This keeps the
denotation of `if (c) return a; …` definitionally `if c then a else …`, so printed
definitions are checked by `rfl`.

`safe` mirrors the denotation and says that a run stays within what the model
covers. At L1 every operation is covered, so it only follows calls.
-/

namespace V2

/-- What follows a statement list: the result when it completes normally, breaks,
or continues. -/
structure K (Γ : Ctx) (R : Type) where
  normal : Γ.denote → R
  brk : Γ.denote → R
  cont : Γ.denote → R

def K.map (f : Γ'.denote → Γ.denote) (k : K Γ R) : K Γ' R := ⟨k.normal ∘ f, k.brk ∘ f, k.cont ∘ f⟩

def K.all (r : Γ.denote → R) : K Γ R := ⟨r, r, r⟩

/-! ## Record literals -/

def Sel.pick : Sel src fs → src.denote → fs.denote
  | .nil, _ => ()
  | .cons i rest, xs => (i.get xs, rest.pick xs)
  | .absent _ rest, xs => (none, rest.pick xs)

def Upd.apply : {fs : Fields} → Upd src fs → src.denote → fs.denote → fs.denote
  | .nil, .nil, _, _ => ()
  | .cons .., .set i rest, xs, (_, r) => (i.get xs, rest.apply xs r)
  | .cons .., .keep _ rest, xs, (a, r) => (a, rest.apply xs r)

/-! ## Expressions -/

mutual
  def TExpr.denote (fs : Φ.denote) : TExpr Φ Γ τ → Γ.denote → τ.denote
    | .bool b, _ => b
    | .int n, _ => n
    | .str s, _ => s
    | .tagLit _, _ => ()
    | .litIn _ _ i, _ => i
    | .undef .., _ => none
    | .null .., _ => none
    | .var v, ρ => v.get ρ
    | .widen N e, ρ => N.embed (e.denote fs ρ)
    | .not e, ρ => !e.denote fs ρ
    | .neg e, ρ => -e.denote fs ρ
    | .add a b, ρ => a.denote fs ρ + b.denote fs ρ
    | .sub a b, ρ => a.denote fs ρ - b.denote fs ρ
    | .mul a b, ρ => a.denote fs ρ * b.denote fs ρ
    | .concat a b, ρ => a.denote fs ρ ++ b.denote fs ρ
    | .eq _ a b, ρ => Ty.beq _ (a.denote fs ρ) (b.denote fs ρ)
    | .ne _ a b, ρ => !Ty.beq _ (a.denote fs ρ) (b.denote fs ρ)
    | .lt a b, ρ => decide (a.denote fs ρ < b.denote fs ρ)
    | .le a b, ρ => decide (a.denote fs ρ ≤ b.denote fs ρ)
    | .gt a b, ρ => decide (b.denote fs ρ < a.denote fs ρ)
    | .ge a b, ρ => decide (b.denote fs ρ ≤ a.denote fs ρ)
    | .slt a b, ρ => strLt (a.denote fs ρ) (b.denote fs ρ)
    | .sle a b, ρ => strLe (a.denote fs ρ) (b.denote fs ρ)
    | .sgt a b, ρ => strLt (b.denote fs ρ) (a.denote fs ρ)
    | .sge a b, ρ => strLe (b.denote fs ρ) (a.denote fs ρ)
    | .and a b, ρ => a.denote fs ρ && b.denote fs ρ
    | .or a b, ρ => a.denote fs ρ || b.denote fs ρ
    | .cond c a b, ρ => if c.denote fs ρ then a.denote fs ρ else b.denote fs ρ
    | .isNull _ e, ρ => (e.denote fs ρ).isNone
    | .notNull _ e, ρ => (e.denote fs ρ).isSome
    | .condNull v _ a b, ρ => match v.get ρ with
      | none => a.denote fs ρ
      | some y => b.denote fs (v.narrowVal ρ y)
    | .condNotNull v _ a b, ρ => match v.get ρ with
      | some y => a.denote fs (v.narrowVal ρ y)
      | none => b.denote fs ρ
    | .coalesce _ a b, ρ => match a.denote fs ρ with
      | some x => x
      | none => b.denote fs ρ
    | .call fn _ args, ρ => fn.get fs (args.denote fs ρ)
    | .record es sel _, ρ => sel.pick (es.denote fs ρ)
    | .update r es u _, ρ => u.apply (es.denote fs ρ) (r.denote fs ρ)
    | .field e i _, ρ => i.get (e.denote fs ρ)

  def TArgs.denote (fs : Φ.denote) : TArgs Φ Γ ps → Γ.denote → ps.denote
    | .nil, _ => ()
    | .cons e rest, ρ => (e.denote fs ρ, rest.denote fs ρ)
    | .omitted _, _ => Ctx.none _

  def TEntries.denote (fs : Φ.denote) : TEntries Φ Γ src → Γ.denote → src.denote
    | .nil, _ => ()
    | .cons _ e rest, ρ => (e.denote fs ρ, rest.denote fs ρ)
end

mutual
  /-- The run stays within what the model covers, evaluating as JavaScript does
  (`&&`, `||`, `??` and `?:` evaluate only the operand they need). -/
  def TExpr.safe (fs : Φ.denote) (ss : Φ.safety) : TExpr Φ Γ τ → Γ.denote → Bool
    | .bool _, _ | .int _, _ | .str _, _ | .tagLit _, _ | .litIn .., _ | .undef .., _ | .null .., _ | .var _, _ => true
    | .widen _ e, ρ | .not e, ρ | .neg e, ρ | .isNull _ e, ρ | .notNull _ e, ρ | .field e _ _, ρ => e.safe fs ss ρ
    | .add a b, ρ | .sub a b, ρ | .mul a b, ρ | .concat a b, ρ | .eq _ a b, ρ | .ne _ a b, ρ
    | .lt a b, ρ | .le a b, ρ | .gt a b, ρ | .ge a b, ρ
    | .slt a b, ρ | .sle a b, ρ | .sgt a b, ρ | .sge a b, ρ => a.safe fs ss ρ && b.safe fs ss ρ
    | .and a b, ρ => a.safe fs ss ρ && (if a.denote fs ρ then b.safe fs ss ρ else true)
    | .or a b, ρ => a.safe fs ss ρ && (if a.denote fs ρ then true else b.safe fs ss ρ)
    | .cond c a b, ρ => c.safe fs ss ρ && (if c.denote fs ρ then a.safe fs ss ρ else b.safe fs ss ρ)
    | .condNull v _ a b, ρ => match v.get ρ with
      | none => a.safe fs ss ρ
      | some y => b.safe fs ss (v.narrowVal ρ y)
    | .condNotNull v _ a b, ρ => match v.get ρ with
      | some y => a.safe fs ss (v.narrowVal ρ y)
      | none => b.safe fs ss ρ
    | .coalesce _ a b, ρ => a.safe fs ss ρ && (match a.denote fs ρ with
      | some _ => true
      | none => b.safe fs ss ρ)
    | .call fn _ args, ρ => args.safe fs ss ρ && fn.safe ss (args.denote fs ρ)
    | .record es _ _, ρ => es.safe fs ss ρ
    | .update r es _ _, ρ => r.safe fs ss ρ && es.safe fs ss ρ

  def TArgs.safe (fs : Φ.denote) (ss : Φ.safety) : TArgs Φ Γ ps → Γ.denote → Bool
    | .nil, _ | .omitted _, _ => true
    | .cons e rest, ρ => e.safe fs ss ρ && rest.safe fs ss ρ

  def TEntries.safe (fs : Φ.denote) (ss : Φ.safety) : TEntries Φ Γ src → Γ.denote → Bool
    | .nil, _ => true
    | .cons _ e rest, ρ => e.safe fs ss ρ && rest.safe fs ss ρ
end

/-! ## Statements -/

mutual
  def TStmts.denote (fs : Φ.denote) : TStmts Φ Γ τ → K Γ τ.denote → Γ.denote → τ.denote
    | .nil, k, ρ => k.normal ρ
    | .const _ e rest, k, ρ => rest.denote fs (k.map Prod.snd) (e.denote fs ρ, ρ)
    | .ret e _, _, ρ => e.denote fs ρ
    | .ite c yes no rest, k, ρ =>
      if c.denote fs ρ then yes.denote fs { k with normal := rest.denote fs k } ρ
      else no.denote fs { k with normal := rest.denote fs k } ρ
    | .block body rest, k, ρ => body.denote fs { k with normal := rest.denote fs k } ρ
    | .brk _, k, ρ => k.brk ρ
    | .ifNull v _ yes no rest, k, ρ => match v.get ρ with
      | none => yes.denote fs { k with normal := rest.denote fs k } ρ
      | some y => no.denote fs (K.map (v.widen some) { k with normal := rest.denote fs k }) (v.narrowVal ρ y)
    | .ifNullExit v _ yes rest, k, ρ => match v.get ρ with
      | none => yes.denote fs k ρ
      | some y => rest.denote fs (k.map (v.widen some)) (v.narrowVal ρ y)
    | .ifNotNull v _ yes no rest, k, ρ => match v.get ρ with
      | some y => yes.denote fs (K.map (v.widen some) { k with normal := rest.denote fs k }) (v.narrowVal ρ y)
      | none => no.denote fs { k with normal := rest.denote fs k } ρ
    | .switchU v _ cases rest, k, ρ =>
      cases.denote fs { k with normal := rest.denote fs k, brk := rest.denote fs k } ρ id (v.get ρ)

  /-- A case runs with the variable narrowed to its variant; `inj` embeds the
  remaining variants into the union. -/
  def TCases.denote {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants}
      {v : Var Γ x (.union key vs0)} {vs : Variants} (fs : Φ.denote) :
      TCases Φ Γ τ v vs → K Γ τ.denote → Γ.denote → (vs.denote → vs0.denote) → vs.denote → τ.denote
    | .one body, k, ρ, inj, y => body.denote fs (k.map (v.widen fun z => inj z.2)) (v.narrowVal ρ ((), y))
    | .cons body more, k, ρ, inj, u => match u with
      | .inl y => body.denote fs (k.map (v.widen fun z => inj (.inl z.2))) (v.narrowVal ρ ((), y))
      | .inr w => more.denote fs k ρ (fun z => inj (.inr z)) w
end

mutual
  def TStmts.safe (fs : Φ.denote) (ss : Φ.safety) : TStmts Φ Γ τ → K Γ Bool → Γ.denote → Bool
    | .nil, k, ρ => k.normal ρ
    | .const _ e rest, k, ρ => e.safe fs ss ρ && rest.safe fs ss (k.map Prod.snd) (e.denote fs ρ, ρ)
    | .ret e _, _, ρ => e.safe fs ss ρ
    | .ite c yes no rest, k, ρ => c.safe fs ss ρ &&
      (if c.denote fs ρ then yes.safe fs ss { k with normal := rest.safe fs ss k } ρ
       else no.safe fs ss { k with normal := rest.safe fs ss k } ρ)
    | .block body rest, k, ρ => body.safe fs ss { k with normal := rest.safe fs ss k } ρ
    | .brk _, k, ρ => k.brk ρ
    | .ifNull v _ yes no rest, k, ρ => match v.get ρ with
      | none => yes.safe fs ss { k with normal := rest.safe fs ss k } ρ
      | some y => no.safe fs ss (K.map (v.widen some) { k with normal := rest.safe fs ss k }) (v.narrowVal ρ y)
    | .ifNullExit v _ yes rest, k, ρ => match v.get ρ with
      | none => yes.safe fs ss k ρ
      | some y => rest.safe fs ss (k.map (v.widen some)) (v.narrowVal ρ y)
    | .ifNotNull v _ yes no rest, k, ρ => match v.get ρ with
      | some y => yes.safe fs ss (K.map (v.widen some) { k with normal := rest.safe fs ss k }) (v.narrowVal ρ y)
      | none => no.safe fs ss { k with normal := rest.safe fs ss k } ρ
    | .switchU v _ cases rest, k, ρ =>
      cases.safe fs ss { k with normal := rest.safe fs ss k, brk := rest.safe fs ss k } ρ id (v.get ρ)

  def TCases.safe {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants}
      {v : Var Γ x (.union key vs0)} {vs : Variants} (fs : Φ.denote) (ss : Φ.safety) :
      TCases Φ Γ τ v vs → K Γ Bool → Γ.denote → (vs.denote → vs0.denote) → vs.denote → Bool
    | .one body, k, ρ, inj, y => body.safe fs ss (k.map (v.widen fun z => inj z.2)) (v.narrowVal ρ ((), y))
    | .cons body more, k, ρ, inj, u => match u with
      | .inl y => body.safe fs ss (k.map (v.widen fun z => inj (.inl z.2))) (v.narrowVal ρ ((), y))
      | .inr w => more.safe fs ss k ρ (fun z => inj (.inr z)) w
end

/-- A function body; falling off the end (excluded by `TProgram.WF`) gives the default. -/
def TStmts.denoteFn (fs : Φ.denote) (body : TStmts Φ Γ τ) : Γ.denote → τ.denote :=
  body.denote fs (K.all fun _ => τ.default)

/-- A function's safety condition: `true` for trivially safe bodies. -/
def TStmts.safeFn (fs : Φ.denote) (ss : Φ.safety) (body : TStmts Φ Γ τ) : Γ.denote → Bool :=
  if body.trivial then fun _ => true else body.safe fs ss (K.all fun _ => true)

/-- Each function denotes in terms of the ones declared before it. -/
def TProgram.denote : TProgram Φ → Φ.denote
  | .nil => ()
  | .cons _ body rest => (body.denoteFn rest.denote, rest.denote)

def TProgram.safety : TProgram Φ → Φ.safety
  | .nil => ()
  | .cons _ body rest => (body.safeFn rest.denote rest.safety, rest.safety)

/-- Assemble a program's denotation from per-function equations, so that checking a
function never unfolds the functions it calls. -/
theorem TProgram.denote_cons {s : Sig} {body : TStmts Φ s.params s.result} {P : TProgram Φ}
    {fs : Φ.denote} {g : s.denote} (hP : P.denote = fs) (hg : body.denoteFn fs = g) :
    (TProgram.cons s body P).denote = (g, fs) := by
  rw [TProgram.denote, hP, hg]

theorem TProgram.safety_cons {s : Sig} {body : TStmts Φ s.params s.result} {P : TProgram Φ}
    {fs : Φ.denote} {ss : Φ.safety} {g : s.params.denote → Bool} (hP : P.denote = fs) (hS : P.safety = ss)
    (hg : body.safeFn fs ss = g) : (TProgram.cons s body P).safety = (g, ss) := by
  rw [TProgram.safety, hP, hS, hg]

/-- Distinct function names, well-formed bodies that return on every path, and no
declaration that shadows (the condition under which `run` models JavaScript's
scoping). -/
def TProgram.WF (P : TProgram Φ) : Prop := P.names.Nodup ∧ P.bodiesOk = true ∧ P.erase.scoped = true

instance (P : TProgram Φ) : Decidable P.WF := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end V2
