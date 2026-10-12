import Ariadne.Shallow.Safety.Erasure.Traversal
import Ariadne.Shallow.Safety.Erasure.Data

namespace Ariadne.Shallow.Safety
open Core

/-- All typed Core values agree with the native interpretation. Function values
are related on related inputs, retaining their invocation guards. -/
theorem term_erases {interp : Named.Interp} (body : Term Γ t)
    (model : Environment Γ interp) (native : Core.Env Γ interp)
    (related : ErasesEnvironment model native) :
    Erases t (term body model).1 (Denote.term body native) := by
  induction body with
  | var v => exact related v
  | unit => rfl
  | bool value => rfl
  | int value => rfl
  | number mantissa exponent => rfl
  | string value => rfl
  | unary op input ih => exact unary_erases op _ _ (ih model native related)
  | binary op left right ihl ihr => exact binary_erases op _ _ _ _ (ihl model native related) (ihr model native related)
  | let_ name input next ihv ihb => exact ihb _ _ (related.cons (ihv model native related))
  | ite condition yes no ihc ihy ihn =>
    have testValue : (term condition model).1 = Denote.term condition native := ihc model native related
    cases value : Denote.term condition native
    · simpa only [term, testValue, Denote.term, value, Bool.false_eq_true, ↓reduceIte] using ihn model native related
    · simpa only [term, testValue, Denote.term, value, ↓reduceIte] using ihy model native related
  | none => trivial
  | some input ih => exact ih model native related
  | optionCase option fallback body iho ihe ihp =>
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
  | sumCase value left right ihv ihl ihr =>
    have values := ihv model native related
    cases hx : (term value model).1 <;> cases hy : Denote.term value native
    all_goals simp only [hx, hy, Erases] at values
    · simpa only [term, Denote.term, hx, hy, Sum.elim_inl] using ihl _ _ (related.cons values)
    · simpa only [term, Denote.term, hx, hy, Sum.elim_inr] using ihr _ _ (related.cons values)
  | pack declaration value ih =>
    exact congrArg (interp declaration).construct (erases_shape_eq declaration.shape _ _ (ih model native related))
  | @unpack Γ declaration value ih =>
    have values : (term value model).1 = Denote.term value native := ih model native related
    apply erases_shape_of_eq declaration.shape
    simp only [term, Denote.term, values, cast_cast, cast_eq]
  | lam name input ih =>
    intro x y h
    exact ih _ _ (related.cons h)
  | app function argument ihf iha => exact ihf model native related _ _ (iha model native related)
  | closed input ih => exact ih () () (by intro t v; cases v)
  | listMap f xs ihf ihx => exact listMap_erases (ihf model native related) (ihx model native related)
  | listFilter f xs ihf ihx => exact listFilter_erases (ihf model native related) (ihx model native related)
  | listReduce f initial xs ihf ihi ihx => exact listReduce_erases (ihf model native related) (ihx model native related) (ihi model native related)
  | listSome f xs ihf ihx => exact listSome_erases (ihf model native related) (ihx model native related)
  | listEvery f xs ihf ihx => exact listEvery_erases (ihf model native related) (ihx model native related)
  | listFind f xs ihf ihx => exact listFind_erases (ihf model native related) (ihx model native related)
  | listFindIndex f xs ihf ihx => exact listFindIndex_erases (ihf model native related) (ihx model native related)
  | listSlice xs start stop ihx iha ihb =>
    have a : (term start model).1 = Denote.term start native := iha model native related
    have b : (term stop model).1 = Denote.term stop native := ihb model native related
    simpa only [term, Denote.term, a, b] using listSlice_erases (ihx model native related) (Denote.term start native) (Denote.term stop native)
  | @mapEmpty Γ k v => cases k <;> exact .nil
  | setEmpty => rfl
  | mapSet m key value ihm ihk ihv =>
    exact mapSet_erases _ _ _ _ _ _ _ (ihm model native related) (ihk model native related) (ihv model native related)
  | next input ih => exact ih model native related
  | stop input ih => exact ih model native related
  | ret input ih => exact ih model native related
  | each xs initial body ihx ihi ihb => exact each_erases (ihb model native related) (ihx model native related) (ihi model native related)
  | exitCase value done returned ihe ihd ihr =>
    have output := ihe model native related
    cases hx : (term value model).1 <;> cases hy : Denote.term value native
    all_goals simp only [hx, hy, Erases] at output
    · simpa only [term, Denote.term, hx, hy, Exit.elim] using ihd model native related _ _ output
    · simpa only [term, Denote.term, hx, hy, Exit.elim] using ihr model native related _ _ output

theorem term_lift_value {interp : Named.Interp} (body : Term Γ t)
    (data : Γ.all dataType = true) (result : dataType t = true) (native : Core.Env Γ interp) :
    cast (data_model t interp result) (term body (liftEnvironment Γ data native)).1 = Denote.term body native :=
  erases_data_eq t result _ _ (term_erases body _ native (ErasesEnvironment.lift Γ data native))

end Ariadne.Shallow.Safety
