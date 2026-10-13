import Ariadne

namespace Tests.Permissions
open Ariadne Ariadne.Shallow Ariadne.Shallow.Adequacy Ariadne.Shallow.Core Ariadne.Heap

private abbrev Row := Core.Ty.pair .int (.pair (.list .int) .unit)
private def rowLayout : DataRelation Value (Row.denote Named.canonical) :=
  (DataRelation.field "count" DataRelation.int
    (DataRelation.field "shared" DataRelation.int.array DataRelation.fieldsNil)).record
private def fields (count : Int) : List (String × Value) :=
  [("count", .bigint count), ("shared", .ref 4)]
private def state : State :=
  { env := [("left", 0), ("right", 2)],
    heap := [.cell (.ref 1), .record (fields 0), .cell (.ref 3),
      .record (fields 7), .array [.bigint 9]] }
private def names : Names [Row, Row] := Names.fromList ["left", "right"]
private def layouts : Layouts [Row, Row] Named.canonical :=
  Layouts.cons rowLayout (Layouts.cons rowLayout (fun {t} (v : Var [] t) => nomatch v))
private def accesses : Accesses [Row, Row] :=
  Accesses.cons (.borrow true) (Accesses.cons .observation (fun {t} (v : Var [] t) => nomatch v))
private def reads : Footprints [Row, Row] :=
  Footprints.cons [1, 4] (Footprints.cons [3, 4] (fun {t} (v : Var [] t) => nomatch v))
private def writes : Footprints [Row, Row] :=
  Footprints.cons [1] (Footprints.cons [] (fun {t} (v : Var [] t) => nomatch v))
private def natives : Core.Env [Row, Row] Named.canonical :=
  ((0, [9], ()), (7, [9], ()), ())

private theorem row_related (root : Nat) (count : Int)
    (lookup : state.heap[root]? = some (.record (fields count))) (distinct : root ≠ 4) :
    rowLayout.Holds state.heap (.ref root) (count, [9], ()) [root, 4] := by
  have array : DataRelation.int.array.Holds state.heap (.ref 4) [9] [4] := by
    refine ⟨by decide, 4, .array [.bigint 9], [], rfl, rfl, ?_, by simp, rfl⟩
    refine ⟨[.bigint 9], rfl, ?_⟩
    exact DataRelation.Elements.cons (r := DataRelation.int) ⟨rfl, rfl⟩ .nil (by simp [Disjoint])
  refine ⟨root, .record (fields count), [4], rfl, lookup, ?_, by simpa using distinct, rfl⟩
  refine ⟨fields count, rfl, .bigint count, rfl, [], [4], ⟨rfl, rfl⟩, ?_, by simp [Disjoint], rfl⟩
  exact ⟨.ref 4, rfl, [4], [], array, ⟨True.intro, rfl⟩, by simp [Disjoint], rfl⟩

private theorem binds_iff (name : String) (address : Nat) :
    state.Binds name address ↔ (name = "left" ∧ address = 0) ∨ (name = "right" ∧ address = 2) := by
  by_cases left : name = "left"
  · subst name; simp [State.Binds, state]; omega
  · by_cases right : name = "right"
    · subst name; simp [State.Binds, state]; omega
    · simp [State.Binds, state, left, right, Ne.symm left, Ne.symm right]

private theorem inputs :
    PermissionEnvironment names (@layouts) (@accesses) (@reads) (@writes) state natives := by
  constructor
  · constructor
    · intro name address bound
      rcases (binds_iff name address).mp bound with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    · intro left right address hl hr
      rcases (binds_iff left address).mp hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals rcases (binds_iff right _).mp hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> first | rfl | omega
  · intro t v scalar visible
    cases v with
    | here => cases scalar
    | there v => cases v with
      | here => cases scalar
      | there v => nomatch v
  · intro t v visible
    cases v with
    | here => exact ⟨.ref 1, rfl, row_related 1 0 rfl (by decide)⟩
    | there v => cases v with
      | here => exact ⟨.ref 3, rfl, row_related 3 7 rfl (by decide)⟩
      | there v => nomatch v
  · intro t v visible
    cases v with
    | here => simp [writes, reads, Footprints.cons]
    | there v => cases v with
      | here => simp [writes, reads, Footprints.cons]
      | there v => nomatch v
  · intro t v visible immutable
    cases v with
    | here => cases immutable
    | there v => cases v with
      | here => rfl
      | there v => nomatch v
  · intro t v visible name address bound
    have cell : address = 0 ∨ address = 2 := by
      rcases (binds_iff name address).mp bound with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    cases v with
    | here => rcases cell with rfl | rfl <;> decide
    | there v => cases v with
      | here => rcases cell with rfl | rfl <;> decide
      | there v => nomatch v
  · intro a b v w hv hw distinct
    cases v with
    | here => cases w with
      | here => exact False.elim (distinct rfl)
      | there w => cases w with
        | here => simp [Disjoint, reads, writes, Footprints.cons]
        | there w => nomatch w
    | there v => cases v with
      | here => cases w with
        | here => simp [Disjoint, reads, writes, Footprints.cons]
        | there w => cases w with
          | here => exact False.elim (distinct rfl)
          | there w => nomatch w
      | there v => nomatch v

-- Both records share address 4, which is readable but never writable here.
theorem shared_reads : 4 ∈ reads (.here : Var [Row, Row] Row) ∧
    4 ∈ reads (.there .here : Var [Row, Row] Row) := by decide

-- Update the borrowed left record without assigning its binding cell or
-- duplicating its native permission; the right record and shared array survive.
theorem borrowed_mutation :
    ∃ after,
      state.write 1 (.record (fieldSet (fields 0) "count" (.bigint 1))) = .ok after ∧
      PermissionEnvironment (names.cons "left")
        (Layouts.cons rowLayout (@layouts))
        (@Accesses.cons [Row, Row] Row (.borrow true) (@accesses))
        (@Footprints.cons [Row, Row] Row [1, 4] (@reads))
        (@Footprints.cons [Row, Row] Row [1] (@writes))
        after ((1, [9], ()), natives) := by
  obtain ⟨actual, after, lookup, written, related, modified⟩ :=
    record_scalar_set "count" (.bigint 1)
      (row_related 1 0 rfl (by decide))
      (IgnoresField.required DataRelation.int.array (IgnoresField.nil "count") (by decide))
      (show (.bigint 1 : Value) = .bigint (1 : Int) from rfl)
  have sameFields : actual = fields 0 := by
    have original : state.heap[1]? = some (.record (fields 0)) := rfl
    rw [original] at lookup
    exact Object.record.inj (Option.some.inj lookup).symm
  subst actual
  have afterEq : after = {state with heap := after.heap} := by
    simp only [State.write, show 1 < state.heap.length from by decide, ↓reduceIte] at written
    cases written
    rfl
  refine ⟨after, written, ?_⟩
  rw [afterEq]
  exact inputs.mutate (.here : Var [Row, Row] Row) rfl [1] (by simp [writes, Footprints.cons])
    after.heap modified (.ref 1) rfl (1, [9], ()) related (fun repr => nomatch repr)

-- Treating the shared immutable array as writable would violate separation.
theorem shared_write_refused :
    ¬ PermissionEnvironment names (@layouts) (@accesses) (@reads)
      (@coarseWrites [Row, Row] (@accesses) (@reads)) state natives := by
  intro invalid
  have separate := invalid.separate (.there .here : Var [Row, Row] Row)
    (.here : Var [Row, Row] Row) rfl rfl (by decide)
  exact separate 4 (by decide) (by decide)

end Tests.Permissions
