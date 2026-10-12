import Ariadne.Shallow.Adequacy.JoinsContext
import Examples.Shallow.scalars

namespace Examples.Proofs.SharedSource
open Ariadne Ariadne.Shallow Ariadne.Shallow.Core Ariadne.Shallow.Adequacy
open Extracted_scalars.Shallow
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def updateFunction : Ariadne.Function := Extracted_scalars.program.functions[1]!
private def updateStatements : List Stmt := match updateFunction.body with | .block ss _ => ss | _ => []
private def updateNames : Names [.int, .int, .bool] := Names.fromList ["x", "y", "flag"]
private def updateAfter : Names [.int, .int, .int, .bool] := updateNames.cons "total"
private def updateContinuation : Term [.int, .int, .int, .bool] .int := .binary .intMul (.var .here) (.int 2)
private def updateSelect : Renaming [.int, .int, .int, .bool]
    [.int, .fn (environmentType [.int, .int, .int, .bool]) .int, .int, .int, .int, .bool]
  | _, .here => .here
  | _, .there .here => .there (.there (.there .here))
  | _, .there (.there .here) => .there (.there (.there (.there .here)))
  | _, .there (.there (.there .here)) => .there (.there (.there (.there (.there .here))))

private theorem updateCapture :
    Captures ((updateAfter.cons "#join").cons "total")
      (Ghosts.skip (Ghosts.bind updateContinuation.abstract (Ghosts.skip Ghosts.empty)))
      updateAfter Ghosts.empty.skip updateSelect := by
  constructor
  · intro t v scalar visible
    cases v with
    | here => exact ⟨rfl, rfl⟩
    | there v =>
      cases v with
      | here => exact ⟨rfl, rfl⟩
      | there v =>
        cases v with
        | here => exact ⟨rfl, rfl⟩
        | there v =>
          cases v with
          | here => exact ⟨rfl, rfl⟩
          | there v => cases v
  · intro t v value found
    cases v with
    | here => cases found
    | there v => cases found

private theorem updateOutside {t} (v : Var [.int, .int, .int, .bool] t) (repr : Scalar t)
    (_ : updateAfter.visible v = true) : updateAfter.get v ∈ ["total", "flag", "y", "x"] := by
  cases v with
  | here => decide
  | there v =>
    cases v with
    | here => decide
    | there v =>
      cases v with
      | here => decide
      | there v =>
        cases v with
        | here => decide
        | there v => cases v

private theorem updateTranslation (interp : Named.Interp) :
    ScalarJoins interp .int (JoinContext updateNames Ghosts.empty ["flag", "y", "x"] [])
      (fun _ _ => False) updateStatements CoreArtifacts.update.body := by
  apply ScalarJoins.contextLet "total" (ScalarExpr.var .int .here _ rfl)
  · simp
  · apply ScalarJoins.contextShared (leading := [updateStatements[1]!])
      (continuation := updateContinuation)
      (suffixPre := JoinContext updateAfter Ghosts.empty.skip ["total", "flag", "y", "x"] []) "#join"
    · exact ScalarJoins.contextReturn
        (ScalarExpr.binary .intMul (ScalarExpr.var .int .here _ rfl) (ScalarExpr.int 2 _) _) _ []
    · apply ScalarJoins.contextIf (ScalarExpr.var .bool (.there (.there (.there (.there .here)))) _ rfl)
      · apply ScalarJoins.contextBlock
        intro saved
        apply ScalarJoins.contextAssign (.there .here) rfl
          (ScalarExpr.binary .intAdd (ScalarExpr.var .int (.there .here) _ rfl)
            (ScalarExpr.var .int (.there (.there (.there .here))) _ rfl) _)
        apply ScalarJoins.contextJump (.there .here) rfl updateSelect (fun s => {s with env := saved})
        intro state env h
        exact (h.capture updateCapture).restore (fun v repr visible => updateOutside v repr visible)
      · apply ScalarJoins.contextBlock
        intro saved
        apply ScalarJoins.contextAssign (.there .here) rfl
          (ScalarExpr.binary .intSub (ScalarExpr.var .int (.there .here) _ rfl)
            (ScalarExpr.var .int (.there (.there (.there .here))) _ rfl) _)
        apply ScalarJoins.contextJump (.there .here) rfl updateSelect (fun s => {s with env := saved})
        intro state env h
        exact (h.capture updateCapture).restore (fun v repr visible => updateOutside v repr visible)



private def scopedFunction : Ariadne.Function := Extracted_scalars.program.functions[8]!
private def scopedStatements : List Stmt := match scopedFunction.body with | .block ss _ => ss | _ => []
private def scopedNames : Names [.int] := Names.fromList ["x"]
private def scopedContinuation : Term [.int] .int :=
  .let_ "temporary" (.binary .intSub (.var .here) (.int 3)) (.var .here)
private def scopedSelect : Renaming [.int] [.int, .int, .fn (environmentType [.int]) .int, .int]
  | _, .here => .here

private theorem scopedCapture :
    Captures (((scopedNames.cons "#join").cons "temporary").cons "x")
      (Ghosts.skip (Ghosts.skip (Ghosts.bind scopedContinuation.abstract Ghosts.empty)))
      scopedNames Ghosts.empty scopedSelect := by
  constructor
  · intro t v scalar visible
    cases v with
    | here => exact ⟨rfl, rfl⟩
    | there v => cases v
  · intro t v value found
    cases found

private theorem scopedTranslation (interp : Named.Interp) :
    ScalarJoins interp .int (JoinContext scopedNames Ghosts.empty ["x"] [])
      (fun _ _ => False) scopedStatements CoreArtifacts.«scoped».body := by
  apply ScalarJoins.contextShared (leading := [scopedStatements[0]!])
    (continuation := scopedContinuation)
    (suffixPre := JoinContext scopedNames Ghosts.empty ["x"] []) "#join"
  · apply ScalarJoins.contextLet "temporary"
      (ScalarExpr.binary .intSub (ScalarExpr.var .int .here _ rfl) (ScalarExpr.int 3 _) _)
    · simp
    · exact ScalarJoins.contextReturn (ScalarExpr.var .int .here _ rfl) _ []
  · apply ScalarJoins.contextBlock
    intro saved
    apply ScalarJoins.contextLet "temporary"
      (ScalarExpr.binary .intAdd (ScalarExpr.var .int (.there .here) _ rfl) (ScalarExpr.int 1 _) _)
    · simp
    · apply ScalarJoins.contextAssign (.there (.there .here)) rfl
        (ScalarExpr.binary .intMul (ScalarExpr.var .int .here _ rfl) (ScalarExpr.int 2 _) _)
      apply ScalarJoins.contextJump (.there (.there .here)) rfl scopedSelect (fun s => {s with env := saved})
      intro state env h
      apply (h.capture scopedCapture).restore
      intro t v repr visible
      cases v with
      | here => exact List.mem_cons_self
      | there v => cases v

/-- The emitted update function agrees with the exact checked source for all
inputs and starting heaps. Both branch assignments share one proved suffix. -/
theorem update_source (x y : Int) (flag : Bool) (heap : Heap) :
    SourceReturnsFrom Extracted_scalars.source "update" heap
      [.bigint x, .bigint y, .boolean flag] (.bigint (update x y flag)) := by
  have related : Environment updateNames
      (bindArguments {heap} updateFunction.params [.bigint x, .bigint y, .boolean flag])
      (interp := Interpretation.value) (x, (y, (flag, ()))) := by
    intro t v repr visible
    cases v with
    | here =>
      cases repr
      apply lookup_declare_other (by decide)
      apply lookup_declare_other (by decide)
      exact lookup_declare_self _ _ _
    | there v =>
      cases v with
      | here =>
        cases repr
        apply lookup_declare_other (by decide)
        exact lookup_declare_self _ _ _
      | there v =>
        cases v with
        | here => cases repr; exact lookup_declare_self _ _ _
        | there v => cases v
  exact scalar_joins_source Extracted_scalars.certificate updateFunction .int CoreArtifacts.update.body
    updateStatements (match updateFunction.body with | .block _ span => span | _ => {})
    (by kernel_rfl) (by kernel_rfl) Interpretation.value
    (JoinContext updateNames Ghosts.empty ["flag", "y", "x"] []) (updateTranslation _)
    (x, (y, (flag, ()))) heap [.bigint x, .bigint y, .boolean flag]
    (JoinContext.initial related (bindArguments_valid _ _ _) rfl)

/-- The inner temporary disappears at scope exit, the write to x survives, and
the source may declare a new temporary with the same name afterwards. -/
theorem scoped_source (x : Int) (heap : Heap) :
    SourceReturnsFrom Extracted_scalars.source "scoped" heap [.bigint x] (.bigint («scoped» x)) := by
  have related : Environment scopedNames (bindArguments {heap} scopedFunction.params [.bigint x])
      (interp := Interpretation.value) (x, ()) := by
    intro t v repr visible
    cases v with
    | here => cases repr; exact lookup_declare_self _ _ _
    | there v => cases v
  exact scalar_joins_source Extracted_scalars.certificate scopedFunction .int CoreArtifacts.«scoped».body
    scopedStatements (match scopedFunction.body with | .block _ span => span | _ => {})
    (by kernel_rfl) (by kernel_rfl) Interpretation.value
    (JoinContext scopedNames Ghosts.empty ["x"] []) (scopedTranslation _)
    (x, ()) heap [.bigint x] (JoinContext.initial related (bindArguments_valid _ _ _) rfl)

end Examples.Proofs.SharedSource
