import Ariadne.Typed.Control
import Ariadne.Typed.Syntax
import Ariadne.Kernel

/-!
# Denotation and safety

Expressions denote functions of the environment tuple. Statement lists denote in
continuation-passing style: `ss.denote fs k ρ` is the function's result when the
list runs in `ρ`, and `k` gives the result of what follows when the list ends
normally, with `break`, or with `continue`. `return` discards `k`. This keeps the
denotation of `if (c) return a; …` definitionally `if c then a else …`, so printed
definitions are checked by `rfl`.

`safe` mirrors the denotation and says that a run stays within what the model
covers: numbers stay safe integers and comparators are consistent.
-/

namespace Ariadne

/-- What follows a statement list: the result when it completes normally, breaks,
or continues. -/
abbrev K (Γ : Ctx) (R : Type) := Control Γ.denote R

abbrev K.map (f : Γ'.denote → Γ.denote) (k : K Γ R) : K Γ' R := Control.map f k

abbrev K.all (r : Γ.denote → R) : K Γ R := Control.all r

/-! ## Record literals -/

def Sel.pick : Sel src fs → src.denote → fs.denote
  | .nil, _ => ()
  | .cons i rest, xs => (i.get xs, rest.pick xs)
  | .absent _ rest, xs => (none, rest.pick xs)

def Upd.apply : {fs : Fields} → Upd src fs → src.denote → fs.denote → fs.denote
  | .nil, .nil, _, _ => ()
  | .cons .., .set i rest, xs, (_, r) => (i.get xs, rest.apply xs r)
  | .cons .., .keep _ rest, xs, (a, r) => (a, rest.apply xs r)

/-! ## Numbers and arrays -/

/-- `a[i]`. -/
def listIndex (xs : List α) (i : Int) : Option α := if 0 ≤ i then xs[i.toNat]? else none

/-- `some`/`find` apply the callback until it returns `true`; each application is safe. -/
def anySafe (p s : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => s x && (p x || anySafe p s xs)

/-- `every` applies the callback until it returns `false`. -/
def allSafe (p s : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => s x && (!p x || allSafe p s xs)

/-- The comparator's signs on every pair of elements, as `toSorted` computes them. -/
def signs (cmp : α → α → Int) (xs : List α) : List (List Int) := xs.map fun x => xs.map fun y => sign (cmp x y)

/-- `toSorted(cmp)`: the stable order of a consistent comparator. -/
def sortedBy (cmp : α → α → Int) (xs : List α) : List α :=
  (sortIndices (signs cmp xs) xs.length).filterMap (xs[·]?)

/-- The comparator is safe on every pair (unless trivially safe, flag `t`) and
consistent on the array. -/
def sortSafe (cmp : α → α → Int) (t : Bool) (s : α → α → Bool) (xs : List α) : Bool :=
  (t || xs.all (fun x => xs.all (s x))) && consistent (signs cmp xs)

/-! ## Expressions -/

/-- An operator's result. -/
def Op.apply : Op σ τ → σ.denote → σ.denote → τ.denote
  | .add, a, b | .nadd, a, b => a + b
  | .sub, a, b | .nsub, a, b => a - b
  | .mul, a, b | .nmul, a, b => a * b
  | .concat, a, b => a ++ b
  | .eq _, a, b => Ty.beq _ a b
  | .ne _, a, b => !Ty.beq _ a b
  | .lt, a, b | .nlt, a, b => decide (a < b)
  | .le, a, b | .nle, a, b => decide (a ≤ b)
  | .gt, a, b | .ngt, a, b => decide (b < a)
  | .ge, a, b | .nge, a, b => decide (b ≤ a)
  | .slt, a, b => strLt a b
  | .sle, a, b => strLe a b
  | .sgt, a, b => strLt b a
  | .sge, a, b => strLe b a
  | .idiv, a, b => a.tdiv b
  | .imod, a, b | .nmod, a, b => a.tmod b
  | .ndiv, a, b => a.fdiv b

def SMethod.apply : SMethod τ → JSString → JSString → τ.denote
  | .startsWith, s, t => strStartsWith s t
  | .endsWith, s, t => strEndsWith s t
  | .includes, s, t => strIncludes s t
  | .indexOf, s, t => strIndexOf s t

/-- An operator's safety condition, given its operands' condition `s`: `number`
arithmetic must stay within the safe integers. -/
def Op.guard : Op σ τ → Bool → σ.denote → σ.denote → Bool
  | .nadd, s, a, b => s && inRange (a + b)
  | .nsub, s, a, b => s && inRange (a - b)
  | .nmul, s, a, b => s && inRange (a * b)
  | .idiv, s, _, b | .imod, s, _, b => s && b != 0
  | .ndiv, s, a, b => s && (b != 0 && inRange a && inRange b)
  | .nmod, s, a, b => s && (b != 0 && inRange (a.tmod b))
  | _, s, _, _ => s

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
    | .bin op a b, ρ => op.apply (a.denote fs ρ) (b.denote fs ρ)
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
    | .num n, _ => n
    | .negNum n _, _ => -n
    | .nneg e, ρ => -e.denote fs ρ
    | .iinc up e, ρ | .ninc up e, ρ => bif up then e.denote fs ρ + 1 else e.denote fs ρ - 1
    | .array es, ρ => es.denote fs ρ
    | .length a, ρ => ((a.denote fs ρ).length : Int)
    | .slength s, ρ => ((s.denote fs ρ).length : Int)
    | .smethod m s t, ρ => m.apply (s.denote fs ρ) (t.denote fs ρ)
    | .slice1 s a, ρ => strSlice (s.denote fs ρ) (a.denote fs ρ) (s.denote fs ρ).length
    | .slice2 s a b, ρ => strSlice (s.denote fs ρ) (a.denote fs ρ) (b.denote fs ρ)
    | .index a i, ρ => listIndex (a.denote fs ρ) (i.denote fs ρ)
    | .includes _ a e, ρ => (a.denote fs ρ).any fun y => Ty.beq _ y (e.denote fs ρ)
    | .any a p, ρ => (a.denote fs ρ).any (p.denote fs ρ)
    | .all a p, ρ => (a.denote fs ρ).all (p.denote fs ρ)
    | .find a p, ρ => (a.denote fs ρ).find? (p.denote fs ρ)
    | .filter a p, ρ => (a.denote fs ρ).filter (p.denote fs ρ)
    | .map a f, ρ => (a.denote fs ρ).map (f.denote fs ρ)
    | .sorted a c, ρ => sortedBy (c.denote fs ρ) (a.denote fs ρ)
    | .newMap _, _ => []
    | .stateGet v i _ k, ρ => mapGet (i.get (v.get ρ)) (k.denote fs ρ)
    | .stateHas v i k, ρ => (mapGet (i.get (v.get ρ)) (k.denote fs ρ)).isSome
    | .stateSize v i, ρ => ((i.get (v.get ρ)).length : Int)
    | .callThis fn v args, ρ => fn.get fs (v.get ρ, args.denote fs ρ)

  def TArgs.denote (fs : Φ.denote) : TArgs Φ Γ ps → Γ.denote → ps.denote
    | .nil, _ => ()
    | .cons e rest, ρ => (e.denote fs ρ, rest.denote fs ρ)
    | .omitted _, _ => Ctx.none _

  def TEntries.denote (fs : Φ.denote) : TEntries Φ Γ src → Γ.denote → src.denote
    | .nil, _ => ()
    | .cons _ e rest, ρ => (e.denote fs ρ, rest.denote fs ρ)

  def TFn.denote (fs : Φ.denote) : TFn Φ Γ τ σ → Γ.denote → τ.denote → σ.denote
    | .arrow _ body, ρ => fun y => body.denote fs (y, ρ)
    | .const body, ρ => fun _ => body.denote fs ρ
    | .ref fn _, _ => fun y => fn.get fs (y, ())

  def TCmp.denote (fs : Φ.denote) : TCmp Φ Γ τ → Γ.denote → τ.denote → τ.denote → Int
    | .arrow _ _ body, ρ => fun y z => body.denote fs (y, z, ρ)
    | .ref fn _, _ => fun y z => fn.get fs (y, z, ())

  def TElems.denote (fs : Φ.denote) : TElems Φ Γ τ → Γ.denote → List τ.denote
    | .nil, _ => []
    | .cons e rest, ρ => e.denote fs ρ :: rest.denote fs ρ
    | .spread a rest, ρ => a.denote fs ρ ++ rest.denote fs ρ
    | .spreadKeys v i rest, ρ => (i.get (v.get ρ)).map Prod.fst ++ rest.denote fs ρ
    | .spreadValues v i rest, ρ => (i.get (v.get ρ)).map Prod.snd ++ rest.denote fs ρ
end

/-- `a && b`, where a static flag marks a conjunct that holds whatever the
environment (it comes from trivially safe syntax): flagged conjuncts are left out,
so a safety condition mentions only the operations that can leave the model. -/
def andT (ta : Bool) (a : Bool) (tb : Bool) (b : Bool) : Bool :=
  if ta then (if tb then true else b) else (if tb then a else a && b)

mutual
  /-- The run stays within what the model covers, evaluating as JavaScript does
  (`&&`, `||`, `??` and `?:` evaluate only the operand they need). A subterm's
  condition is consulted only when the subterm is not trivially safe. -/
  def TExpr.safe (fs : Φ.denote) (ss : Φ.safety) : TExpr Φ Γ τ → Γ.denote → Bool
    | .bool _, _ | .int _, _ | .str _, _ | .tagLit _, _ | .litIn .., _ | .undef .., _ | .null .., _ | .var _, _
    | .num _, _ | .negNum .., _ => true
    | .widen _ e, ρ | .not e, ρ | .neg e, ρ | .isNull _ e, ρ | .notNull _ e, ρ | .field e _ _, ρ | .iinc _ e, ρ
    | .length e, ρ | .slength e, ρ => e.safe fs ss ρ
    | .index a b, ρ | .includes _ a b, ρ | .smethod _ a b, ρ | .slice1 a b, ρ =>
      andT a.trivial (a.safe fs ss ρ) b.trivial (b.safe fs ss ρ)
    | .slice2 s a b, ρ => andT s.trivial (s.safe fs ss ρ) (a.trivial && b.trivial)
      (andT a.trivial (a.safe fs ss ρ) b.trivial (b.safe fs ss ρ))
    | .bin op a b, ρ => op.guard (andT a.trivial (a.safe fs ss ρ) b.trivial (b.safe fs ss ρ))
      (a.denote fs ρ) (b.denote fs ρ)
    | .nneg e, ρ => (e.trivial || e.safe fs ss ρ) && inRange (-e.denote fs ρ)
    | .ninc up e, ρ => (e.trivial || e.safe fs ss ρ) &&
      inRange (bif up then e.denote fs ρ + 1 else e.denote fs ρ - 1)
    | .and a b, ρ => andT a.trivial (a.safe fs ss ρ) b.trivial (if a.denote fs ρ then b.safe fs ss ρ else true)
    | .or a b, ρ => andT a.trivial (a.safe fs ss ρ) b.trivial (if a.denote fs ρ then true else b.safe fs ss ρ)
    | .cond c a b, ρ => andT c.trivial (c.safe fs ss ρ) (a.trivial && b.trivial)
      (if c.denote fs ρ then a.trivial || a.safe fs ss ρ else b.trivial || b.safe fs ss ρ)
    | .condNull v _ a b, ρ => match v.get ρ with
      | none => a.trivial || a.safe fs ss ρ
      | some y => b.trivial || b.safe fs ss (v.narrowVal ρ y)
    | .condNotNull v _ a b, ρ => match v.get ρ with
      | some y => a.trivial || a.safe fs ss (v.narrowVal ρ y)
      | none => b.trivial || b.safe fs ss ρ
    | .coalesce _ a b, ρ => andT a.trivial (a.safe fs ss ρ) b.trivial (match a.denote fs ρ with
      | some _ => true
      | none => b.safe fs ss ρ)
    | @TExpr.call _ _ _ s fn _ args, ρ => andT args.trivial (args.safe fs ss ρ) s.trivial (fn.safe ss (args.denote fs ρ))
    | .record es _ _, ρ | .array es, ρ => es.safe fs ss ρ
    | .update r es _ _, ρ => andT r.trivial (r.safe fs ss ρ) es.trivial (es.safe fs ss ρ)
    | .any a p, ρ | .find a p, ρ => andT a.trivial (a.safe fs ss ρ) p.trivial
      (anySafe (p.denote fs ρ) (p.safe fs ss ρ) (a.denote fs ρ))
    | .all a p, ρ => andT a.trivial (a.safe fs ss ρ) p.trivial
      (allSafe (p.denote fs ρ) (p.safe fs ss ρ) (a.denote fs ρ))
    | .filter a p, ρ | .map a p, ρ => andT a.trivial (a.safe fs ss ρ) p.trivial ((a.denote fs ρ).all (p.safe fs ss ρ))
    | .sorted a c, ρ => (a.trivial || a.safe fs ss ρ) &&
      sortSafe (c.denote fs ρ) c.trivial (c.safe fs ss ρ) (a.denote fs ρ)
    | .newMap _, _ | .stateSize _ _, _ => true
    | .stateGet _ _ _ k, ρ | .stateHas _ _ k, ρ => k.safe fs ss ρ
    | .callThis (t := t) fn v args, ρ =>
      andT args.trivial (args.safe fs ss ρ) t (fn.safe ss (v.get ρ, args.denote fs ρ))

  def TArgs.safe (fs : Φ.denote) (ss : Φ.safety) : TArgs Φ Γ ps → Γ.denote → Bool
    | .nil, _ | .omitted _, _ => true
    | .cons e rest, ρ => andT e.trivial (e.safe fs ss ρ) rest.trivial (rest.safe fs ss ρ)

  def TEntries.safe (fs : Φ.denote) (ss : Φ.safety) : TEntries Φ Γ src → Γ.denote → Bool
    | .nil, _ => true
    | .cons _ e rest, ρ => andT e.trivial (e.safe fs ss ρ) rest.trivial (rest.safe fs ss ρ)

  def TFn.safe (fs : Φ.denote) (ss : Φ.safety) : TFn Φ Γ τ σ → Γ.denote → τ.denote → Bool
    | .arrow _ body, ρ => fun y => body.safe fs ss (y, ρ)
    | .const body, ρ => fun _ => body.safe fs ss ρ
    | .ref fn _, _ => fun y => fn.safe ss (y, ())

  def TCmp.safe (fs : Φ.denote) (ss : Φ.safety) : TCmp Φ Γ τ → Γ.denote → τ.denote → τ.denote → Bool
    | .arrow _ _ body, ρ => fun y z => body.safe fs ss (y, z, ρ)
    | .ref fn _, _ => fun y z => fn.safe ss (y, z, ())

  def TElems.safe (fs : Φ.denote) (ss : Φ.safety) : TElems Φ Γ τ → Γ.denote → Bool
    | .nil, _ => true
    | .cons e rest, ρ | .spread e rest, ρ => andT e.trivial (e.safe fs ss ρ) rest.trivial (rest.safe fs ss ρ)
    | .spreadKeys _ _ rest, ρ | .spreadValues _ _ rest, ρ => rest.safe fs ss ρ
end

/-! ## Statements -/

/-- A loop over `items` in continuation-passing style: `step y next exit` runs an
iteration on `y`, continuing with `next` (the remaining iterations) or leaving the
loop with `exit`; after the last iteration, `exit`. The state is the environment. -/
def forIn {α σ R : Type} (items : List α) (step : α → (σ → R) → (σ → R) → σ → R) (exit : σ → R) : σ → R :=
  items.foldr (fun y next => step y next exit) exit

/-- A `while` loop in continuation-passing style, for at most `n` more iterations: while `cond`
holds, `step next exit` runs an iteration, continuing with `next` or leaving with `exit`; once `cond`
fails, `exit`. A loop still running after `n` iterations gives `stuck`. -/
def whileIn {σ R : Type} : Nat → (σ → Bool) → ((σ → R) → (σ → R) → σ → R) → (σ → R) → (σ → R) → σ → R
  | 0, _, _, _, stuck, s => stuck s
  | n + 1, cond, step, exit, stuck, s => if cond s then step (whileIn n cond step exit stuck) exit s else exit s

/-- The iterations a `while` loop may run: its safety condition says that it ends within them. -/
def loopBound : Nat := 2 ^ 64

/-- A `while` loop's result. Should it run past `loopBound` iterations it leaves (which its safety
condition excludes). -/
def whileDo.def {σ R : Type} (cond : σ → Bool) (step : (σ → R) → (σ → R) → σ → R) (exit : σ → R) (s : σ) : R :=
  whileIn loopBound cond step exit exit s

/-- A `while` loop's safety condition: every iteration is safe, and it ends within `loopBound`. -/
def whileSafe.def {σ : Type} (cond : σ → Bool) (step : (σ → Bool) → (σ → Bool) → σ → Bool) (exit : σ → Bool)
    (s : σ) : Bool :=
  whileIn loopBound cond step exit (fun _ => false) s

/- `whileDo` and `whileSafe` are these definitions with the kernel's lowest unfolding priority. A per-file
check compares a readable definition with the denotation; the kernel unfolds the side whose head has the
greater height first, and the denotation reaches the loop through `&&` and other small definitions. With
an ordinary height, the kernel would unfold the readable side's loop first, through `loopBound` iterations;
with the lowest, it unfolds the denotation until both sides are the same loop, and compares the
arguments. -/
open Lean in
run_meta do
  for (n, src) in [(`Ariadne.whileDo, ``whileDo.def), (`Ariadne.whileSafe, ``whileSafe.def)] do
    let info ← getConstInfoDefn src
    let decl := Declaration.defnDecl { info with name := n, value := mkConst src, hints := .opaque }
    addDecl decl
    compileDecl decl

theorem whileDo_def {σ R : Type} (cond : σ → Bool) (step : (σ → R) → (σ → R) → σ → R) (exit : σ → R) (s : σ) :
    whileDo cond step exit s = whileIn loopBound cond step exit exit s := rfl

theorem whileSafe_def {σ : Type} (cond : σ → Bool) (step : (σ → Bool) → (σ → Bool) → σ → Bool)
    (exit : σ → Bool) (s : σ) : whileSafe cond step exit s = whileIn loopBound cond step exit (fun _ => false) s :=
  rfl

/-- `0 … n-1`, the values a counted loop's index takes. -/
def range (n : Int) : List Int := (List.range n.toNat).map Int.ofNat

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
    | .let_ _ e rest, k, ρ => rest.denote fs (k.map Prod.snd) (e.denote fs ρ, ρ)
    | .assign v e rest, k, ρ => rest.denote fs k (v.set ρ (e.denote fs ρ))
    | .cont _, k, ρ => k.cont ρ
    | .forOf _ a body rest, k, ρ =>
      forIn (a.denote fs ρ) (fun y next exit ρ' => body.denote fs (K.map Prod.snd ⟨next, exit, next⟩) (y, ρ'))
        (rest.denote fs k) ρ
    | .forEntries _ _ a body rest, k, ρ =>
      forIn (a.denote fs ρ).zipIdx (fun p next exit ρ' =>
          body.denote fs (K.map Prod.snd (K.map Prod.snd ⟨next, exit, next⟩)) (p.1, (p.2 : Int), ρ'))
        (rest.denote fs k) ρ
    | .ifNull v _ yes no rest, k, ρ => match v.get ρ with
      | none => yes.denote fs { k with normal := rest.denote fs k } ρ
      | some y => no.denote fs (K.map (v.widen some) { k with normal := rest.denote fs k }) (v.narrowVal ρ y)
    | .ifNullExit v _ yes rest, k, ρ => match v.get ρ with
      | none => yes.denote fs k ρ
      | some y => rest.denote fs (k.map (v.widen some)) (v.narrowVal ρ y)
    | .ifNotNull v _ yes no rest, k, ρ => match v.get ρ with
      | some y => yes.denote fs (K.map (v.widen some) { k with normal := rest.denote fs k }) (v.narrowVal ρ y)
      | none => no.denote fs { k with normal := rest.denote fs k } ρ
    | .switchG v _ arms rest, k, ρ =>
      Variants.elim _ (v.get ρ) fun i y =>
        arms.denote fs { k with normal := rest.denote fs k, brk := rest.denote fs k } ρ i y (rest.denote fs k ρ)
    | .forRange _ v body rest, k, ρ =>
      forIn (range (v.get ρ)) (fun j next exit ρ' => body.denote fs (K.map Prod.snd ⟨next, exit, next⟩) (j, ρ'))
        (rest.denote fs k) ρ
    | .whileLoop c body rest, k, ρ =>
      whileDo (fun ρ' => c.denote fs ρ') (fun next exit ρ' => body.denote fs ⟨next, exit, next⟩ ρ') (rest.denote fs k) ρ
    | .stateSet v i _ key e rest, k, ρ =>
      rest.denote fs k (v.set ρ (i.set (v.get ρ) (mapPut (i.get (v.get ρ)) (key.denote fs ρ) (e.denote fs ρ))))
    | .stateDelete v i _ key rest, k, ρ =>
      rest.denote fs k (v.set ρ (i.set (v.get ρ) (mapDel (i.get (v.get ρ)) (key.denote fs ρ))))
    | .callVoid fn v args rest, k, ρ => rest.denote fs k (v.set ρ (fn.get fs (v.get ρ, args.denote fs ρ)))
    | .retVoid v _, _, ρ => v.get ρ

  /-- Running the cases from this one on (after a match). -/
  def TArms.first {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} (fs : Φ.denote) : TArms Φ Γ τ v → K Γ τ.denote → Γ.denote → τ.denote
    | .nil, k, ρ => k.normal ρ
    | .empty _ rest, k, ρ => rest.first fs k ρ
    | .wide _ body _, k, ρ => body.denote fs k ρ
    | .narrow _ _ _, k, ρ => k.normal ρ

  /-- The case for the variant `i` (tagged `t`): the first case labelled `t`, else
  `default` (`d`, the run from the last `default` seen so far). -/
  def TArms.denote {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} {t : TagLit} {fds : Fields} (fs : Φ.denote) :
      TArms Φ Γ τ v → K Γ τ.denote → Γ.denote → VIdx vs0 t fds → fds.denote → τ.denote → τ.denote
    | .nil, _, _, _, _, d => d
    | .empty l rest, k, ρ, i, y, d =>
      if l = some t then rest.first fs k ρ else rest.denote fs k ρ i y (if l = none then rest.first fs k ρ else d)
    | .wide l body rest, k, ρ, i, y, d =>
      if l = some t then body.denote fs k ρ else rest.denote fs k ρ i y (if l = none then body.denote fs k ρ else d)
    | .narrow i' body rest, k, ρ, i, y, d => match i'.proj (i.inj y) with
      | some y' => body.denote fs (k.map (v.widen fun z => i'.inj z.2)) (v.narrowVal ρ ((), y'))
      | none => rest.denote fs k ρ i y d
end

mutual
  def TStmts.safe (fs : Φ.denote) (ss : Φ.safety) : TStmts Φ Γ τ → K Γ Bool → Γ.denote → Bool
    | .nil, k, ρ => k.normal ρ
    | .const _ e rest, k, ρ => (e.trivial || e.safe fs ss ρ) && rest.safe fs ss (k.map Prod.snd) (e.denote fs ρ, ρ)
    | .ret e _, _, ρ => e.trivial || e.safe fs ss ρ
    | .ite c yes no rest, k, ρ => (c.trivial || c.safe fs ss ρ) &&
      (if c.denote fs ρ then yes.safe fs ss { k with normal := rest.safe fs ss k } ρ
       else no.safe fs ss { k with normal := rest.safe fs ss k } ρ)
    | .block body rest, k, ρ => body.safe fs ss { k with normal := rest.safe fs ss k } ρ
    | .brk _, k, ρ => k.brk ρ
    | .let_ _ e rest, k, ρ => (e.trivial || e.safe fs ss ρ) && rest.safe fs ss (k.map Prod.snd) (e.denote fs ρ, ρ)
    | .assign v e rest, k, ρ => (e.trivial || e.safe fs ss ρ) && rest.safe fs ss k (v.set ρ (e.denote fs ρ))
    | .cont _, k, ρ => k.cont ρ
    | .forOf _ a body rest, k, ρ => (a.trivial || a.safe fs ss ρ) &&
      forIn (a.denote fs ρ) (fun y next exit ρ' => body.safe fs ss (K.map Prod.snd ⟨next, exit, next⟩) (y, ρ'))
        (rest.safe fs ss k) ρ
    | .forEntries _ _ a body rest, k, ρ => (a.trivial || a.safe fs ss ρ) &&
      forIn (a.denote fs ρ).zipIdx (fun p next exit ρ' =>
          body.safe fs ss (K.map Prod.snd (K.map Prod.snd ⟨next, exit, next⟩)) (p.1, (p.2 : Int), ρ'))
        (rest.safe fs ss k) ρ
    | .ifNull v _ yes no rest, k, ρ => match v.get ρ with
      | none => yes.safe fs ss { k with normal := rest.safe fs ss k } ρ
      | some y => no.safe fs ss (K.map (v.widen some) { k with normal := rest.safe fs ss k }) (v.narrowVal ρ y)
    | .ifNullExit v _ yes rest, k, ρ => match v.get ρ with
      | none => yes.safe fs ss k ρ
      | some y => rest.safe fs ss (k.map (v.widen some)) (v.narrowVal ρ y)
    | .ifNotNull v _ yes no rest, k, ρ => match v.get ρ with
      | some y => yes.safe fs ss (K.map (v.widen some) { k with normal := rest.safe fs ss k }) (v.narrowVal ρ y)
      | none => no.safe fs ss { k with normal := rest.safe fs ss k } ρ
    | .switchG v _ arms rest, k, ρ =>
      Variants.elim _ (v.get ρ) fun i y =>
        arms.safe fs ss { k with normal := rest.safe fs ss k, brk := rest.safe fs ss k } ρ i y (rest.safe fs ss k ρ)
    | .forRange _ v body rest, k, ρ =>
      forIn (range (v.get ρ)) (fun j next exit ρ' => body.safe fs ss (K.map Prod.snd ⟨next, exit, next⟩) (j, ρ'))
        (rest.safe fs ss k) ρ
    | .whileLoop c body rest, k, ρ =>
      whileSafe (fun ρ' => c.denote fs ρ') (fun next exit ρ' => body.safe fs ss ⟨next, exit, next⟩ ρ') (rest.safe fs ss k) ρ
    | .stateSet v i _ key e rest, k, ρ => andT key.trivial (key.safe fs ss ρ) e.trivial (e.safe fs ss ρ) &&
      rest.safe fs ss k (v.set ρ (i.set (v.get ρ) (mapPut (i.get (v.get ρ)) (key.denote fs ρ) (e.denote fs ρ))))
    | .stateDelete v i _ key rest, k, ρ => (key.trivial || key.safe fs ss ρ) &&
      rest.safe fs ss k (v.set ρ (i.set (v.get ρ) (mapDel (i.get (v.get ρ)) (key.denote fs ρ))))
    | .callVoid (t := t) fn v args rest, k, ρ =>
      andT args.trivial (args.safe fs ss ρ) t (fn.safe ss (v.get ρ, args.denote fs ρ)) &&
        rest.safe fs ss k (v.set ρ (fn.get fs (v.get ρ, args.denote fs ρ)))
    | .retVoid _ _, _, _ => true

  def TArms.firstSafe {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} (fs : Φ.denote) (ss : Φ.safety) : TArms Φ Γ τ v → K Γ Bool → Γ.denote → Bool
    | .nil, k, ρ => k.normal ρ
    | .empty _ rest, k, ρ => rest.firstSafe fs ss k ρ
    | .wide _ body _, k, ρ => body.safe fs ss k ρ
    | .narrow _ _ _, k, ρ => k.normal ρ

  def TArms.safe {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} {t : TagLit} {fds : Fields} (fs : Φ.denote) (ss : Φ.safety) :
      TArms Φ Γ τ v → K Γ Bool → Γ.denote → VIdx vs0 t fds → fds.denote → Bool → Bool
    | .nil, _, _, _, _, d => d
    | .empty l rest, k, ρ, i, y, d =>
      if l = some t then rest.firstSafe fs ss k ρ
      else rest.safe fs ss k ρ i y (if l = none then rest.firstSafe fs ss k ρ else d)
    | .wide l body rest, k, ρ, i, y, d =>
      if l = some t then body.safe fs ss k ρ
      else rest.safe fs ss k ρ i y (if l = none then body.safe fs ss k ρ else d)
    | .narrow i' body rest, k, ρ, i, y, d => match i'.proj (i.inj y) with
      | some y' => body.safe fs ss (k.map (v.widen fun z => i'.inj z.2)) (v.narrowVal ρ ((), y'))
      | none => rest.safe fs ss k ρ i y d
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

end Ariadne
