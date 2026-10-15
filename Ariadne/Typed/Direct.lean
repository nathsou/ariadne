import Ariadne.Typed.Denote

/-!
# Loops in direct style

The readable definitions are checked, by `rfl`, against a denotation. `TStmts.denote` gives every loop in
continuation-passing style: `forIn items step exit s`, where `step y next exit s` continues with `next` or
leaves with `exit`. That is what a loop that may `break` or `return` needs, but most loops do neither: each
iteration updates the variables and goes on. `TStmts.denoteD` is the same denotation, except that such a
loop (its body `direct`: no `return` anywhere, no `break` of its own) is a fold,

  `rest (items.foldl (fun s y => body y s) s)`,

with the body in direct style: it ends with the variables' new values. Its result type is any `R`, with
`r` giving a `return`'s result, so that a direct body can end with the environment itself.

`TStmts.denoteFn_eq` (in `Ariadne.Proof.Direct`) proves the two denotations equal, once for every
program. A generated file checks its readable definitions against `denoteD`, and so against `denote`.
-/

namespace Ariadne

/-- `items.foldl step init`, with the initial state first (so that its type is known when the step
elaborates): how a readable definition writes a loop whose body is `direct`. -/
@[reducible] def fold {σ α : Type} (init : σ) (items : List α) (step : σ → α → σ) : σ := items.foldl step init

mutual
  /-- No `return` anywhere (in nested loops and `switch` cases too). -/
  def TStmts.noRet : TStmts Φ Γ τ → Bool
    | .nil => true
    | .const _ _ rest => rest.noRet
    | .ret _ _ => false
    | .ite _ yes no rest => yes.noRet && no.noRet && rest.noRet
    | .block body rest => body.noRet && rest.noRet
    | .brk rest => rest.noRet
    | .let_ _ _ rest => rest.noRet
    | .assign _ _ rest => rest.noRet
    | .cont rest => rest.noRet
    | .forOf _ _ body rest => body.noRet && rest.noRet
    | .forEntries _ _ _ body rest => body.noRet && rest.noRet
    | .ifNull _ _ yes no rest => yes.noRet && no.noRet && rest.noRet
    | .ifNullExit _ _ yes rest => yes.noRet && rest.noRet
    | .ifNotNull _ _ yes no rest => yes.noRet && no.noRet && rest.noRet
    | .switchG _ _ arms rest => arms.noRet && rest.noRet
    | .forRange _ _ body rest => body.noRet && rest.noRet
    | .whileLoop _ body rest => body.noRet && rest.noRet
    | .stateSet _ _ _ _ _ rest => rest.noRet
    | .stateDelete _ _ _ _ rest => rest.noRet
    | .callVoid _ _ _ rest => rest.noRet
    | .retVoid _ _ => false

  def TArms.noRet {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)} :
      TArms Φ Γ τ v → Bool
    | .nil => true
    | .empty _ rest => rest.noRet
    | .wide _ body rest => body.noRet && rest.noRet
    | .narrow _ body rest => body.noRet && rest.noRet
end

/-- No `break` of the enclosing loop: none at this level. A nested loop's body and a `switch`'s cases have
`break`s of their own. -/
def TStmts.noBrk : TStmts Φ Γ τ → Bool
  | .nil => true
  | .const _ _ rest => rest.noBrk
  | .ret _ rest => rest.noBrk
  | .ite _ yes no rest => yes.noBrk && no.noBrk && rest.noBrk
  | .block body rest => body.noBrk && rest.noBrk
  | .brk _ => false
  | .let_ _ _ rest => rest.noBrk
  | .assign _ _ rest => rest.noBrk
  | .cont rest => rest.noBrk
  | .forOf _ _ _ rest => rest.noBrk
  | .forEntries _ _ _ _ rest => rest.noBrk
  | .ifNull _ _ yes no rest => yes.noBrk && no.noBrk && rest.noBrk
  | .ifNullExit _ _ yes rest => yes.noBrk && rest.noBrk
  | .ifNotNull _ _ yes no rest => yes.noBrk && no.noBrk && rest.noBrk
  | .switchG _ _ _ rest => rest.noBrk
  | .forRange _ _ _ rest => rest.noBrk
  | .whileLoop _ _ rest => rest.noBrk
  | .stateSet _ _ _ _ _ rest => rest.noBrk
  | .stateDelete _ _ _ _ rest => rest.noBrk
  | .callVoid _ _ _ rest => rest.noBrk
  | .retVoid _ rest => rest.noBrk

/-- A loop body read in direct style: every iteration ends by going on to the next (no `return`, no `break`). -/
def TStmts.direct (body : TStmts Φ Γ τ) : Bool := body.noRet && body.noBrk

mutual
  /-- `TStmts.denote` with any result type (`r`: a `return`'s result), and loops whose body is `direct` as
  folds. -/
  def TStmts.denoteD (fs : Φ.denote) {R : Type} (r : τ.denote → R) : TStmts Φ Γ τ → K Γ R → Γ.denote → R
    | .nil, k, ρ => k.normal ρ
    | .const _ e rest, k, ρ => rest.denoteD fs r (k.map Prod.snd) (e.denote fs ρ, ρ)
    | .ret e _, _, ρ => r (e.denote fs ρ)
    | .ite c yes no rest, k, ρ =>
      if c.denote fs ρ then yes.denoteD fs r { k with normal := rest.denoteD fs r k } ρ
      else no.denoteD fs r { k with normal := rest.denoteD fs r k } ρ
    | .block body rest, k, ρ => body.denoteD fs r { k with normal := rest.denoteD fs r k } ρ
    | .brk _, k, ρ => k.brk ρ
    | .let_ _ e rest, k, ρ => rest.denoteD fs r (k.map Prod.snd) (e.denote fs ρ, ρ)
    | .assign v e rest, k, ρ => rest.denoteD fs r k (v.set ρ (e.denote fs ρ))
    | .cont _, k, ρ => k.cont ρ
    | .forOf _ a body rest, k, ρ =>
      if body.direct then
        rest.denoteD fs r k ((a.denote fs ρ).foldl
          (fun ρ' y => body.denoteD fs (fun _ => ρ') (K.map Prod.snd (K.all id)) (y, ρ')) ρ)
      else
        forIn (a.denote fs ρ) (fun y next exit ρ' => body.denoteD fs r (K.map Prod.snd ⟨next, exit, next⟩) (y, ρ'))
          (rest.denoteD fs r k) ρ
    | .forEntries _ _ a body rest, k, ρ =>
      if body.direct then
        rest.denoteD fs r k ((a.denote fs ρ).zipIdx.foldl
          (fun ρ' p => body.denoteD fs (fun _ => ρ') (K.map Prod.snd (K.map Prod.snd (K.all id)))
            (p.1, (p.2 : Int), ρ')) ρ)
      else
        forIn (a.denote fs ρ).zipIdx (fun p next exit ρ' =>
            body.denoteD fs r (K.map Prod.snd (K.map Prod.snd ⟨next, exit, next⟩)) (p.1, (p.2 : Int), ρ'))
          (rest.denoteD fs r k) ρ
    | .ifNull v _ yes no rest, k, ρ => match v.get ρ with
      | none => yes.denoteD fs r { k with normal := rest.denoteD fs r k } ρ
      | some y => no.denoteD fs r (K.map (v.widen some) { k with normal := rest.denoteD fs r k }) (v.narrowVal ρ y)
    | .ifNullExit v _ yes rest, k, ρ => match v.get ρ with
      | none => yes.denoteD fs r k ρ
      | some y => rest.denoteD fs r (k.map (v.widen some)) (v.narrowVal ρ y)
    | .ifNotNull v _ yes no rest, k, ρ => match v.get ρ with
      | some y => yes.denoteD fs r (K.map (v.widen some) { k with normal := rest.denoteD fs r k }) (v.narrowVal ρ y)
      | none => no.denoteD fs r { k with normal := rest.denoteD fs r k } ρ
    | .switchG v _ arms rest, k, ρ =>
      Variants.elim _ (v.get ρ) fun i y =>
        arms.denoteD fs r { k with normal := rest.denoteD fs r k, brk := rest.denoteD fs r k } ρ i y
          (rest.denoteD fs r k ρ)
    | .forRange _ v body rest, k, ρ =>
      if body.direct then
        rest.denoteD fs r k ((range (v.get ρ)).foldl
          (fun ρ' j => body.denoteD fs (fun _ => ρ') (K.map Prod.snd (K.all id)) (j, ρ')) ρ)
      else
        forIn (range (v.get ρ)) (fun j next exit ρ' => body.denoteD fs r (K.map Prod.snd ⟨next, exit, next⟩) (j, ρ'))
          (rest.denoteD fs r k) ρ
    | .whileLoop c body rest, k, ρ =>
      whileDo (fun ρ' => c.denote fs ρ') (fun next exit ρ' => body.denoteD fs r ⟨next, exit, next⟩ ρ')
        (rest.denoteD fs r k) ρ
    | .stateSet v i _ key e rest, k, ρ =>
      rest.denoteD fs r k (v.set ρ (i.set (v.get ρ) (mapPut (i.get (v.get ρ)) (key.denote fs ρ) (e.denote fs ρ))))
    | .stateDelete v i _ key rest, k, ρ =>
      rest.denoteD fs r k (v.set ρ (i.set (v.get ρ) (mapDel (i.get (v.get ρ)) (key.denote fs ρ))))
    | .callVoid fn v args rest, k, ρ => rest.denoteD fs r k (v.set ρ (fn.get fs (v.get ρ, args.denote fs ρ)))
    | .retVoid v _, _, ρ => r (v.get ρ)

  def TArms.firstD {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
      (fs : Φ.denote) {R : Type} (r : τ.denote → R) : TArms Φ Γ τ v → K Γ R → Γ.denote → R
    | .nil, k, ρ => k.normal ρ
    | .empty _ rest, k, ρ => rest.firstD fs r k ρ
    | .wide _ body _, k, ρ => body.denoteD fs r k ρ
    | .narrow _ _ _, k, ρ => k.normal ρ

  def TArms.denoteD {Φ : Sigs} {Γ : Ctx} {τ : Ty} {x key : String} {vs0 : Variants} {v : Var Γ x (.union key vs0)}
      {t : TagLit} {fds : Fields} (fs : Φ.denote) {R : Type} (r : τ.denote → R) :
      TArms Φ Γ τ v → K Γ R → Γ.denote → VIdx vs0 t fds → fds.denote → R → R
    | .nil, _, _, _, _, d => d
    | .empty l rest, k, ρ, i, y, d =>
      if l = some t then rest.firstD fs r k ρ else rest.denoteD fs r k ρ i y (if l = none then rest.firstD fs r k ρ else d)
    | .wide l body rest, k, ρ, i, y, d =>
      if l = some t then body.denoteD fs r k ρ
      else rest.denoteD fs r k ρ i y (if l = none then body.denoteD fs r k ρ else d)
    | .narrow i' body rest, k, ρ, i, y, d => match i'.proj (i.inj y) with
      | some y' => body.denoteD fs r (k.map (v.widen fun z => i'.inj z.2)) (v.narrowVal ρ ((), y'))
      | none => rest.denoteD fs r k ρ i y d
end

/-- A function body in the direct-style denotation. -/
def TStmts.denoteDFn (fs : Φ.denote) (body : TStmts Φ Γ τ) : Γ.denote → τ.denote :=
  body.denoteD fs id (K.all fun _ => τ.default)

end Ariadne
