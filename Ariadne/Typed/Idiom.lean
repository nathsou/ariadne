import Ariadne.Typed.Direct

/-!
# Idiomatic state: only the variables a statement assigns

`TStmts.denoteD` threads the whole environment through a loop, and readable definitions printed from it
carry every variable in scope: `Ariadne.fold (total, xs, ()) xs (fun (total, xs, ()) x => …)`.
`TStmts.denoteR` is the same denotation, except that a loop's state, and the value an `if` (or a
null test, or a `switch`) leaves when all its branches complete normally, are only the variables the
statement assigns (`writes`), as a flat tuple (`Ctx.tup`): `Ariadne.fold total xs (fun total x => …)`,
`let s := if c then … else …`. The other variables keep the values they had before the statement:
`Ctx.merge m ρ s` puts the state `s` back into the environment `ρ`.

`TStmts.denoteFn_eq_R` (in `Ariadne.Proof.Idiom`) proves the two denotations equal, once for every
program: a statement leaves the variables it does not assign alone (`TStmts.denoteD_frame`).
-/

namespace Ariadne

/-! ## Masks: sets of positions in a context -/

/-- Positions in a context, innermost first; a missing flag is `false`. -/
abbrev Mask := List Bool

def Mask.or : Mask → Mask → Mask
  | [], m => m
  | a :: m, [] => a :: m
  | a :: m, b :: m' => (a || b) :: Mask.or m m'

/-- The position a variable refers to. -/
def Var.mask : Var Γ x τ → Mask
  | .here => [true]
  | .there _ v => false :: v.mask

mutual
  /-- The variables of the context a statement list may assign (directly, or in a nested statement or loop,
  or through `this`); code after `return`, `break` and `continue` is not run. -/
  def TStmts.writes : TStmts Φ Γ τ → Mask
    | .nil => []
    | .const _ _ rest => rest.writes.tail
    | .ret _ _ => []
    | .ite _ yes no rest => Mask.or yes.writes (Mask.or no.writes rest.writes)
    | .block body rest => Mask.or body.writes rest.writes
    | .brk _ => []
    | .let_ _ _ rest => rest.writes.tail
    | .assign v _ rest => Mask.or v.mask rest.writes
    | .cont _ => []
    | .forOf _ _ body rest => Mask.or body.writes.tail rest.writes
    | .forEntries _ _ _ body rest => Mask.or body.writes.tail.tail rest.writes
    | .ifNull _ _ yes no rest => Mask.or yes.writes (Mask.or no.writes rest.writes)
    | .ifNullExit _ _ yes rest => Mask.or yes.writes rest.writes
    | .ifNotNull _ _ yes no rest => Mask.or yes.writes (Mask.or no.writes rest.writes)
    | .switchG _ _ arms rest => Mask.or arms.writes rest.writes
    | .forRange _ _ body rest => Mask.or body.writes.tail rest.writes
    | .whileLoop _ body rest => Mask.or body.writes rest.writes
    | .stateSet v _ _ _ _ rest => Mask.or v.mask rest.writes
    | .stateDelete v _ _ _ rest => Mask.or v.mask rest.writes
    | .callVoid _ v _ rest => Mask.or v.mask rest.writes
    | .retVoid _ _ => []

  def TArms.writes {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      TArms Φ Γ τ v → Mask
    | .nil => []
    | .empty _ rest => rest.writes
    | .wide _ body rest => Mask.or body.writes rest.writes
    | .narrow _ body rest => Mask.or body.writes rest.writes
end

mutual
  /-- No `continue` of the enclosing loop: none outside nested loops (a `switch`'s cases continue the loop
  around it). -/
  def TStmts.noCont : TStmts Φ Γ τ → Bool
    | .nil => true
    | .const _ _ rest => rest.noCont
    | .ret _ rest => rest.noCont
    | .ite _ yes no rest => yes.noCont && no.noCont && rest.noCont
    | .block body rest => body.noCont && rest.noCont
    | .brk rest => rest.noCont
    | .let_ _ _ rest => rest.noCont
    | .assign _ _ rest => rest.noCont
    | .cont _ => false
    | .forOf _ _ _ rest => rest.noCont
    | .forEntries _ _ _ _ rest => rest.noCont
    | .ifNull _ _ yes no rest => yes.noCont && no.noCont && rest.noCont
    | .ifNullExit _ _ yes rest => yes.noCont && rest.noCont
    | .ifNotNull _ _ yes no rest => yes.noCont && no.noCont && rest.noCont
    | .switchG _ _ arms rest => arms.noCont && rest.noCont
    | .forRange _ _ _ rest => rest.noCont
    | .whileLoop _ _ rest => rest.noCont
    | .stateSet _ _ _ _ _ rest => rest.noCont
    | .stateDelete _ _ _ _ rest => rest.noCont
    | .callVoid _ _ _ rest => rest.noCont
    | .retVoid _ rest => rest.noCont

  def TArms.noCont {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      TArms Φ Γ τ v → Bool
    | .nil => true
    | .empty _ rest => rest.noCont
    | .wide _ body rest => body.noCont && rest.noCont
    | .narrow _ body rest => body.noCont && rest.noCont
end

/-- A branch that always completes normally: no `return`, `break` or `continue` of its own. -/
def TStmts.closed (st : TStmts Φ Γ τ) : Bool := st.noRet && st.noBrk && st.noCont

/-- `switch` cases that always go on after the `switch` (a `break` does). -/
def TArms.closed {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
    (arms : TArms Φ Γ τ v) : Bool := arms.noRet && arms.noCont

/-! ## States: the assigned variables as a flat tuple -/

/-- The bindings at the positions of the mask. -/
@[reducible] def Ctx.sub : Ctx → Mask → Ctx
  | [], _ => []
  | _ :: _, [] => []
  | p :: Γ, true :: m => p :: Ctx.sub Γ m
  | _ :: Γ, false :: m => Ctx.sub Γ m

/-- The values of the bindings as a flat tuple: `Unit`, a single value, or a pair whose last
component is the last value (no trailing `()`). -/
@[reducible] def Ctx.tup : Ctx → Type
  | [] => Unit
  | [(_, τ)] => τ.denote
  | (_, τ) :: p :: Γ => τ.denote × Ctx.tup (p :: Γ)

def Ctx.tcons : {x : String} → {τ : Ty} → {Δ : Ctx} → τ.denote → Δ.tup → Ctx.tup ((x, τ) :: Δ)
  | _, _, [], a, _ => a
  | _, _, _ :: _, a, t => (a, t)

def Ctx.thead : {x : String} → {τ : Ty} → {Δ : Ctx} → Ctx.tup ((x, τ) :: Δ) → τ.denote
  | _, _, [], a => a
  | _, _, _ :: _, (a, _) => a

def Ctx.ttail : {x : String} → {τ : Ty} → {Δ : Ctx} → Ctx.tup ((x, τ) :: Δ) → Δ.tup
  | _, _, [], _ => ()
  | _, _, _ :: _, (_, t) => t

/-- The state: the values at the mask's positions. -/
def Ctx.proj : (Γ : Ctx) → (m : Mask) → Γ.denote → (Γ.sub m).tup
  | [], _, _ => ()
  | _ :: _, [], _ => ()
  | (_, _) :: Γ, true :: m, (a, ρ) => Ctx.tcons a (Ctx.proj Γ m ρ)
  | (_, _) :: Γ, false :: m, (_, ρ) => Ctx.proj Γ m ρ

/-- The environment `ρ` with the mask's positions taken from the state `s`. -/
def Ctx.merge : (Γ : Ctx) → (m : Mask) → Γ.denote → (Γ.sub m).tup → Γ.denote
  | [], _, ρ, _ => ρ
  | _ :: _, [], ρ, _ => ρ
  | (_, _) :: Γ, true :: m, (_, ρ), s => (Ctx.thead s, Ctx.merge Γ m ρ (Ctx.ttail s))
  | (_, _) :: Γ, false :: m, (a, ρ), s => (a, Ctx.merge Γ m ρ s)

/-! ## The denotation with states -/

mutual
  /-- `TStmts.denoteD` with states that hold only the assigned variables: a loop's, and the value of an
  `if`, null test or `switch` whose branches all complete normally. -/
  def TStmts.denoteR (fs : Φ.denote) {R : Type} (r : τ.denote → R) : TStmts Φ Γ τ → K Γ R → Γ.denote → R
    | .nil, k, ρ => k.normal ρ
    | .const _ e rest, k, ρ => rest.denoteR fs r (k.map Prod.snd) (e.denote fs ρ, ρ)
    | .ret e _, _, ρ => r (e.denote fs ρ)
    | .ite c yes no rest, k, ρ =>
      if yes.closed && no.closed then
        rest.denoteR fs r k (Γ.merge (Mask.or yes.writes no.writes) ρ
          (if c.denote fs ρ then
            yes.denoteR fs (fun _ => Γ.proj (Mask.or yes.writes no.writes) ρ) (K.all (Γ.proj (Mask.or yes.writes no.writes))) ρ
          else
            no.denoteR fs (fun _ => Γ.proj (Mask.or yes.writes no.writes) ρ) (K.all (Γ.proj (Mask.or yes.writes no.writes))) ρ))
      else if c.denote fs ρ then yes.denoteR fs r { k with normal := rest.denoteR fs r k } ρ
      else no.denoteR fs r { k with normal := rest.denoteR fs r k } ρ
    | .block body rest, k, ρ => body.denoteR fs r { k with normal := rest.denoteR fs r k } ρ
    | .brk _, k, ρ => k.brk ρ
    | .let_ _ e rest, k, ρ => rest.denoteR fs r (k.map Prod.snd) (e.denote fs ρ, ρ)
    | .assign v e rest, k, ρ => rest.denoteR fs r k (v.set ρ (e.denote fs ρ))
    | .cont _, k, ρ => k.cont ρ
    | .forOf _ a body rest, k, ρ =>
      if body.direct then
        rest.denoteR fs r k (Γ.merge body.writes.tail ρ ((a.denote fs ρ).foldl
          (fun s y => body.denoteR fs (fun _ => s) (K.map Prod.snd (K.all (Γ.proj body.writes.tail)))
            (y, Γ.merge body.writes.tail ρ s))
          (Γ.proj body.writes.tail ρ)))
      else
        forIn (a.denote fs ρ) (fun y next exit s =>
            body.denoteR fs r (K.map Prod.snd ⟨next ∘ Γ.proj body.writes.tail, exit ∘ Γ.proj body.writes.tail,
              next ∘ Γ.proj body.writes.tail⟩) (y, Γ.merge body.writes.tail ρ s))
          (fun s => rest.denoteR fs r k (Γ.merge body.writes.tail ρ s)) (Γ.proj body.writes.tail ρ)
    | .forEntries _ _ a body rest, k, ρ =>
      if body.direct then
        rest.denoteR fs r k (Γ.merge body.writes.tail.tail ρ ((a.denote fs ρ).zipIdx.foldl
          (fun s p => body.denoteR fs (fun _ => s)
            (K.map Prod.snd (K.map Prod.snd (K.all (Γ.proj body.writes.tail.tail))))
            (p.1, (p.2 : Int), Γ.merge body.writes.tail.tail ρ s))
          (Γ.proj body.writes.tail.tail ρ)))
      else
        forIn (a.denote fs ρ).zipIdx (fun p next exit s =>
            body.denoteR fs r (K.map Prod.snd (K.map Prod.snd ⟨next ∘ Γ.proj body.writes.tail.tail,
              exit ∘ Γ.proj body.writes.tail.tail, next ∘ Γ.proj body.writes.tail.tail⟩))
              (p.1, (p.2 : Int), Γ.merge body.writes.tail.tail ρ s))
          (fun s => rest.denoteR fs r k (Γ.merge body.writes.tail.tail ρ s)) (Γ.proj body.writes.tail.tail ρ)
    | .ifNull v _ yes no rest, k, ρ =>
      if yes.closed && no.closed then
        rest.denoteR fs r k (Γ.merge (Mask.or yes.writes no.writes) ρ (match v.get ρ with
          | none => yes.denoteR fs (fun _ => Γ.proj (Mask.or yes.writes no.writes) ρ)
              (K.all (Γ.proj (Mask.or yes.writes no.writes))) ρ
          | some y => no.denoteR fs (fun _ => Γ.proj (Mask.or yes.writes no.writes) ρ)
              (K.map (v.widen some) (K.all (Γ.proj (Mask.or yes.writes no.writes)))) (v.narrowVal ρ y)))
      else match v.get ρ with
        | none => yes.denoteR fs r { k with normal := rest.denoteR fs r k } ρ
        | some y => no.denoteR fs r (K.map (v.widen some) { k with normal := rest.denoteR fs r k }) (v.narrowVal ρ y)
    | .ifNullExit v _ yes rest, k, ρ => match v.get ρ with
      | none => yes.denoteR fs r k ρ
      | some y => rest.denoteR fs r (k.map (v.widen some)) (v.narrowVal ρ y)
    | .ifNotNull v _ yes no rest, k, ρ =>
      if yes.closed && no.closed then
        rest.denoteR fs r k (Γ.merge (Mask.or yes.writes no.writes) ρ (match v.get ρ with
          | some y => yes.denoteR fs (fun _ => Γ.proj (Mask.or yes.writes no.writes) ρ)
              (K.map (v.widen some) (K.all (Γ.proj (Mask.or yes.writes no.writes)))) (v.narrowVal ρ y)
          | none => no.denoteR fs (fun _ => Γ.proj (Mask.or yes.writes no.writes) ρ)
              (K.all (Γ.proj (Mask.or yes.writes no.writes))) ρ))
      else match v.get ρ with
        | some y => yes.denoteR fs r (K.map (v.widen some) { k with normal := rest.denoteR fs r k }) (v.narrowVal ρ y)
        | none => no.denoteR fs r { k with normal := rest.denoteR fs r k } ρ
    | .switchG v _ arms rest, k, ρ =>
      if arms.closed then
        rest.denoteR fs r k (Γ.merge arms.writes ρ (Variants.elim _ (v.get ρ) fun i y =>
          arms.denoteR fs (fun _ => Γ.proj arms.writes ρ) (K.all (Γ.proj arms.writes)) ρ i y (Γ.proj arms.writes ρ)))
      else
        Variants.elim _ (v.get ρ) fun i y =>
          arms.denoteR fs r { k with normal := rest.denoteR fs r k, brk := rest.denoteR fs r k } ρ i y
            (rest.denoteR fs r k ρ)
    | .forRange _ v body rest, k, ρ =>
      if body.direct then
        rest.denoteR fs r k (Γ.merge body.writes.tail ρ ((range (v.get ρ)).foldl
          (fun s j => body.denoteR fs (fun _ => s) (K.map Prod.snd (K.all (Γ.proj body.writes.tail)))
            (j, Γ.merge body.writes.tail ρ s))
          (Γ.proj body.writes.tail ρ)))
      else
        forIn (range (v.get ρ)) (fun j next exit s =>
            body.denoteR fs r (K.map Prod.snd ⟨next ∘ Γ.proj body.writes.tail, exit ∘ Γ.proj body.writes.tail,
              next ∘ Γ.proj body.writes.tail⟩) (j, Γ.merge body.writes.tail ρ s))
          (fun s => rest.denoteR fs r k (Γ.merge body.writes.tail ρ s)) (Γ.proj body.writes.tail ρ)
    | .whileLoop c body rest, k, ρ =>
      whileDo (fun s => c.denote fs (Γ.merge body.writes ρ s))
        (fun next exit s => body.denoteR fs r ⟨next ∘ Γ.proj body.writes, exit ∘ Γ.proj body.writes,
          next ∘ Γ.proj body.writes⟩ (Γ.merge body.writes ρ s))
        (fun s => rest.denoteR fs r k (Γ.merge body.writes ρ s)) (Γ.proj body.writes ρ)
    | .stateSet v i _ key e rest, k, ρ =>
      rest.denoteR fs r k (v.set ρ (i.set (v.get ρ) (mapPut (i.get (v.get ρ)) (key.denote fs ρ) (e.denote fs ρ))))
    | .stateDelete v i _ key rest, k, ρ =>
      rest.denoteR fs r k (v.set ρ (i.set (v.get ρ) (mapDel (i.get (v.get ρ)) (key.denote fs ρ))))
    | .callVoid fn v args rest, k, ρ => rest.denoteR fs r k (v.set ρ (fn.get fs (v.get ρ, args.denote fs ρ)))
    | .retVoid v _, _, ρ => r (v.get ρ)

  def TArms.firstR {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
      (fs : Φ.denote) {R : Type} (r : τ.denote → R) : TArms Φ Γ τ v → K Γ R → Γ.denote → R
    | .nil, k, ρ => k.normal ρ
    | .empty _ rest, k, ρ => rest.firstR fs r k ρ
    | .wide _ body _, k, ρ => body.denoteR fs r k ρ
    | .narrow _ _ _, k, ρ => k.normal ρ

  def TArms.denoteR {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
      {t : TagLit} {fds : Fields} (fs : Φ.denote) {R : Type} (r : τ.denote → R) :
      TArms Φ Γ τ v → K Γ R → Γ.denote → VIdx vs0 t fds → fds.denote → R → R
    | .nil, _, _, _, _, d => d
    | .empty l rest, k, ρ, i, y, d =>
      if l = some t then rest.firstR fs r k ρ else rest.denoteR fs r k ρ i y (if l = none then rest.firstR fs r k ρ else d)
    | .wide l body rest, k, ρ, i, y, d =>
      if l = some t then body.denoteR fs r k ρ
      else rest.denoteR fs r k ρ i y (if l = none then body.denoteR fs r k ρ else d)
    | .narrow i' body rest, k, ρ, i, y, d => match i'.proj (i.inj y) with
      | some y' => body.denoteR fs r (k.map (v.widen fun z => i'.inj z.2)) (v.narrowVal ρ ((), y'))
      | none => rest.denoteR fs r k ρ i y d
end

/-- A function body in the denotation with states. -/
def TStmts.denoteRFn (fs : Φ.denote) (body : TStmts Φ Γ τ) : Γ.denote → τ.denote :=
  body.denoteR fs id (K.all fun _ => τ.default)

/-! ## The safety condition with states

`TStmts.safeR` is `TStmts.safe` with a loop threading only the variables its body assigns, and with the
statements after an `if`, a null test or a `switch` a join point taking only the variables its branches
assign. `TStmts.safe_eq_R` (`Ariadne/Proof/Idiom.lean`) proves them equal. -/

/-- The continuation after branches that assign `m`: `then` from the state the branches leave. -/
abbrev Ctx.join (Γ : Ctx) (m : Mask) (ρ : Γ.denote) (after : Γ.denote → Bool) (ρ' : Γ.denote) : Bool :=
  after (Γ.merge m ρ (Γ.proj m ρ'))

mutual
  def TStmts.safeR (fs : Φ.denote) (ss : Φ.safety) : TStmts Φ Γ τ → K Γ Bool → Γ.denote → Bool
    | .nil, k, ρ => k.normal ρ
    | .const _ e rest, k, ρ => (e.trivial || e.safe fs ss ρ) && rest.safeR fs ss (k.map Prod.snd) (e.denote fs ρ, ρ)
    | .ret e _, _, ρ => e.trivial || e.safe fs ss ρ
    | .ite c yes no rest, k, ρ => (c.trivial || c.safe fs ss ρ) &&
      (if c.denote fs ρ then
        yes.safeR fs ss { k with normal := Γ.join (Mask.or yes.writes no.writes) ρ (rest.safeR fs ss k) } ρ
       else no.safeR fs ss { k with normal := Γ.join (Mask.or yes.writes no.writes) ρ (rest.safeR fs ss k) } ρ)
    | .block body rest, k, ρ => body.safeR fs ss { k with normal := rest.safeR fs ss k } ρ
    | .brk _, k, ρ => k.brk ρ
    | .let_ _ e rest, k, ρ => (e.trivial || e.safe fs ss ρ) && rest.safeR fs ss (k.map Prod.snd) (e.denote fs ρ, ρ)
    | .assign v e rest, k, ρ => (e.trivial || e.safe fs ss ρ) && rest.safeR fs ss k (v.set ρ (e.denote fs ρ))
    | .cont _, k, ρ => k.cont ρ
    | .forOf _ a body rest, k, ρ => (a.trivial || a.safe fs ss ρ) &&
      forIn (a.denote fs ρ) (fun y next exit s =>
          body.safeR fs ss (K.map Prod.snd ⟨next ∘ Γ.proj body.writes.tail, exit ∘ Γ.proj body.writes.tail,
            next ∘ Γ.proj body.writes.tail⟩) (y, Γ.merge body.writes.tail ρ s))
        (fun s => rest.safeR fs ss k (Γ.merge body.writes.tail ρ s)) (Γ.proj body.writes.tail ρ)
    | .forEntries _ _ a body rest, k, ρ => (a.trivial || a.safe fs ss ρ) &&
      forIn (a.denote fs ρ).zipIdx (fun p next exit s =>
          body.safeR fs ss (K.map Prod.snd (K.map Prod.snd ⟨next ∘ Γ.proj body.writes.tail.tail,
            exit ∘ Γ.proj body.writes.tail.tail, next ∘ Γ.proj body.writes.tail.tail⟩))
            (p.1, (p.2 : Int), Γ.merge body.writes.tail.tail ρ s))
        (fun s => rest.safeR fs ss k (Γ.merge body.writes.tail.tail ρ s)) (Γ.proj body.writes.tail.tail ρ)
    | .ifNull v _ yes no rest, k, ρ => match v.get ρ with
      | none => yes.safeR fs ss { k with normal := Γ.join (Mask.or yes.writes no.writes) ρ (rest.safeR fs ss k) } ρ
      | some y => no.safeR fs ss
          (K.map (v.widen some) { k with normal := Γ.join (Mask.or yes.writes no.writes) ρ (rest.safeR fs ss k) })
          (v.narrowVal ρ y)
    | .ifNullExit v _ yes rest, k, ρ => match v.get ρ with
      | none => yes.safeR fs ss k ρ
      | some y => rest.safeR fs ss (k.map (v.widen some)) (v.narrowVal ρ y)
    | .ifNotNull v _ yes no rest, k, ρ => match v.get ρ with
      | some y => yes.safeR fs ss
          (K.map (v.widen some) { k with normal := Γ.join (Mask.or yes.writes no.writes) ρ (rest.safeR fs ss k) })
          (v.narrowVal ρ y)
      | none => no.safeR fs ss { k with normal := Γ.join (Mask.or yes.writes no.writes) ρ (rest.safeR fs ss k) } ρ
    | .switchG v _ arms rest, k, ρ =>
      Variants.elim _ (v.get ρ) fun i y =>
        arms.safeR fs ss { k with
            normal := Γ.join arms.writes ρ (rest.safeR fs ss k), brk := Γ.join arms.writes ρ (rest.safeR fs ss k) }
          ρ i y (rest.safeR fs ss k ρ)
    | .forRange _ v body rest, k, ρ =>
      forIn (range (v.get ρ)) (fun j next exit s =>
          body.safeR fs ss (K.map Prod.snd ⟨next ∘ Γ.proj body.writes.tail, exit ∘ Γ.proj body.writes.tail,
            next ∘ Γ.proj body.writes.tail⟩) (j, Γ.merge body.writes.tail ρ s))
        (fun s => rest.safeR fs ss k (Γ.merge body.writes.tail ρ s)) (Γ.proj body.writes.tail ρ)
    | .whileLoop c body rest, k, ρ =>
      whileSafe (fun s => c.denote fs (Γ.merge body.writes ρ s))
        (fun next exit s => body.safeR fs ss ⟨next ∘ Γ.proj body.writes, exit ∘ Γ.proj body.writes,
          next ∘ Γ.proj body.writes⟩ (Γ.merge body.writes ρ s))
        (fun s => rest.safeR fs ss k (Γ.merge body.writes ρ s)) (Γ.proj body.writes ρ)
    | .stateSet v i _ key e rest, k, ρ => andT key.trivial (key.safe fs ss ρ) e.trivial (e.safe fs ss ρ) &&
      rest.safeR fs ss k (v.set ρ (i.set (v.get ρ) (mapPut (i.get (v.get ρ)) (key.denote fs ρ) (e.denote fs ρ))))
    | .stateDelete v i _ key rest, k, ρ => (key.trivial || key.safe fs ss ρ) &&
      rest.safeR fs ss k (v.set ρ (i.set (v.get ρ) (mapDel (i.get (v.get ρ)) (key.denote fs ρ))))
    | .callVoid (t := t) fn v args rest, k, ρ =>
      andT args.trivial (args.safe fs ss ρ) t (fn.safe ss (v.get ρ, args.denote fs ρ)) &&
        rest.safeR fs ss k (v.set ρ (fn.get fs (v.get ρ, args.denote fs ρ)))
    | .retVoid _ _, _, _ => true

  def TArms.firstSafeR {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
      (fs : Φ.denote) (ss : Φ.safety) : TArms Φ Γ τ v → K Γ Bool → Γ.denote → Bool
    | .nil, k, ρ => k.normal ρ
    | .empty _ rest, k, ρ => rest.firstSafeR fs ss k ρ
    | .wide _ body _, k, ρ => body.safeR fs ss k ρ
    | .narrow _ _ _, k, ρ => k.normal ρ

  def TArms.safeR {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
      {t : TagLit} {fds : Fields} (fs : Φ.denote) (ss : Φ.safety) :
      TArms Φ Γ τ v → K Γ Bool → Γ.denote → VIdx vs0 t fds → fds.denote → Bool → Bool
    | .nil, _, _, _, _, d => d
    | .empty l rest, k, ρ, i, y, d =>
      if l = some t then rest.firstSafeR fs ss k ρ
      else rest.safeR fs ss k ρ i y (if l = none then rest.firstSafeR fs ss k ρ else d)
    | .wide l body rest, k, ρ, i, y, d =>
      if l = some t then body.safeR fs ss k ρ
      else rest.safeR fs ss k ρ i y (if l = none then body.safeR fs ss k ρ else d)
    | .narrow i' body rest, k, ρ, i, y, d => match i'.proj (i.inj y) with
      | some y' => body.safeR fs ss (k.map (v.widen fun z => i'.inj z.2)) (v.narrowVal ρ ((), y'))
      | none => rest.safeR fs ss k ρ i y d
end

/-- A function body's safety condition with states. -/
def TStmts.safeRFn (fs : Φ.denote) (ss : Φ.safety) (body : TStmts Φ Γ τ) : Γ.denote → Bool :=
  if body.trivial then fun _ => true else body.safeR fs ss (K.all fun _ => true)

end Ariadne
