import Examples.Proofs.ReferenceDecision
import Ariadne.Shallow.Adequacy.WPTactic

/-!
# The decision function, transferred to its TypeScript source

`choose` from `examples/reference/decision.ts`, run by the original evaluator on
an array of candidate records, returns `undefined` exactly when the emitted
`choose` returns `none`, and otherwise returns one of the input records, which
represents the emitted result.
-/

namespace Examples.ReferenceSource.Decision
open Ariadne Ariadne.Shallow Ariadne.Shallow.Adequacy Extracted_reference_decision.Shallow
open Examples.Proofs.ReferenceDecision (pick choose_fold)

abbrev P := Extracted_reference_decision.program
abbrev Candidate := NativeTypes.«Candidate»

def validKind : JSString := [118, 97, 108, 105, 100]
def rejectedKind : JSString := [114, 101, 106, 101, 99, 116, 101, 100]

/-- A candidate record: its `kind` tag, then its variant's fields. -/
def CandidateAt (heap : Heap) (address : Nat) : Candidate → Prop
  | .valid c => ∃ fields, heap[address]? = some (.record fields) ∧
      fields.lookup "kind" = some (.string validKind) ∧
      fields.lookup "version" = some (.number (Float.Model.ofInt c.version)) ∧
      fields.lookup "id" = some (.string c.id) ∧ Int53.InRange c.version
  | .rejected c => ∃ fields, heap[address]? = some (.record fields) ∧
      fields.lookup "kind" = some (.string rejectedKind) ∧ fields.lookup "reason" = some (.string c.reason)

/-- The value `best` holds: nothing yet, or one of the input records representing a valid candidate. -/
def BestAt (heap : Heap) (refs : List Nat) (value : Value) : Option Candidate → Prop
  | none => value = .undefined
  | some c => ∃ address, value = .ref address ∧ address ∈ refs ∧ CandidateAt heap address c ∧
      ∃ v, c = .valid v

theorem CandidateAt.extend {heap heap' : Heap} {address : Nat} {c : Candidate}
    (at_ : CandidateAt heap address c) (agree : ∀ i, i < heap.length → heap'[i]? = heap[i]?) :
    CandidateAt heap' address c := by
  have bound {o : Object} (h : heap[address]? = some o) : address < heap.length :=
    (List.getElem?_eq_some_iff.mp h).choose
  cases c with
  | valid c =>
    obtain ⟨fields, lookup, rest⟩ := at_
    exact ⟨fields, (agree _ (bound lookup)).trans lookup, rest⟩
  | rejected c =>
    obtain ⟨fields, lookup, rest⟩ := at_
    exact ⟨fields, (agree _ (bound lookup)).trans lookup, rest⟩

/-- Two lists related element by element. -/
inductive Elementwise (R : α → β → Prop) : List α → List β → Prop where
  | nil : Elementwise R [] []
  | cons : R a b → Elementwise R as bs → Elementwise R (a :: as) (b :: bs)

/-! ## The function and its loop body -/

def chooseFn : Ariadne.Function := P.functions[0]!
theorem chooseFind : P.functions.find? (fun f => f.name == chooseFn.name) = some chooseFn := by kernel_rfl
theorem chooseName : chooseFn.name = "choose" := by kernel_rfl

def loopBody : Stmt :=
  match chooseFn.body with
  | .block [_, .forOf _ _ _ body _, _] _ => body
  | _ => default

/-- The loop state: the frame's bindings, an unchanged input heap, and `best`. -/
structure Frame (s : State) (heap0 : Heap) (refs : List Nat) (cA fA bA : Nat) (floor : Int)
    (best : Option Candidate) : Prop where
  env : s.env = [("best", bA), ("floor", fA), ("candidates", cA)]
  inputs : ∀ i, i < heap0.length → s.heap[i]? = heap0[i]?
  order : heap0.length ≤ cA ∧ cA < fA ∧ fA < bA ∧ bA < s.heap.length
  floorCell : s.heap[fA]? = some (.cell (.number (Float.Model.ofInt floor)))
  bestCell : ∃ v, s.heap[bA]? = some (.cell v) ∧ BestAt heap0 refs v best

theorem getElem_of_some {heap : Heap} {i : Nat} {o : Object} (h : heap[i]? = some o) :
    ∃ bound : i < heap.length, heap[i] = o :=
  ⟨(List.getElem?_eq_some_iff.mp h).choose, (List.getElem?_eq_some_iff.mp h).choose_spec⟩

/-- Appending to the heap keeps the frame. -/
theorem Frame.append {s : State} {heap0 : Heap} {refs : List Nat} {cA fA bA : Nat} {floor : Int}
    {best : Option Candidate} (frame : Frame s heap0 refs cA fA bA floor best) (extra : List Object) :
    Frame { env := s.env, heap := s.heap ++ extra } heap0 refs cA fA bA floor best := by
  obtain ⟨o1, o2, o3, o4⟩ := frame.order
  obtain ⟨v, cell, rel⟩ := frame.bestCell
  refine ⟨frame.env, fun i hi => ?_, ⟨o1, o2, o3, by simp; omega⟩, ?_, ⟨v, ?_, rel⟩⟩
  · rw [List.getElem?_append_left (by omega)]; exact frame.inputs i hi
  · rw [List.getElem?_append_left (by omega)]; exact frame.floorCell
  · rw [List.getElem?_append_left (by omega)]; exact cell

/-- Rebinding `best` after appending keeps the frame for the new choice. -/
theorem Frame.rebind {s : State} {heap0 : Heap} {refs : List Nat} {cA fA bA : Nat} {floor : Int}
    {best : Option Candidate} (frame : Frame s heap0 refs cA fA bA floor best) (extra : List Object)
    (v : Value) (best' : Option Candidate) (rel : BestAt heap0 refs v best') :
    Frame { env := s.env, heap := (s.heap ++ extra).set bA (.cell v) } heap0 refs cA fA bA floor best' := by
  obtain ⟨o1, o2, o3, o4⟩ := frame.order
  refine ⟨frame.env, fun i hi => ?_, ⟨o1, o2, o3, by simp; omega⟩, ?_, ⟨v, ?_, rel⟩⟩
  · rw [List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega)]; exact frame.inputs i hi
  · rw [List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega)]; exact frame.floorCell
  · rw [List.getElem?_set_self (by simp; omega)]

theorem Frame.rebind' {s : State} {heap0 : Heap} {refs : List Nat} {cA fA bA : Nat} {floor : Int}
    {best : Option Candidate} (frame : Frame s heap0 refs cA fA bA floor best) (extra : List Object)
    (v : Value) (best' : Option Candidate) (rel : BestAt heap0 refs v best') :
    Frame { env := s.env, heap := s.heap.set bA (.cell v) ++ extra } heap0 refs cA fA bA floor best' := by
  have order := frame.order
  have same : s.heap.set bA (.cell v) ++ extra = (s.heap ++ extra).set bA (.cell v) := by
    rw [List.set_append_left _ _ (by omega)]
  rw [same]
  exact frame.rebind extra v best' rel

set_option maxHeartbeats 4000000 in
theorem iteration (s : State) (heap0 : Heap) (refs : List Nat) (cA fA bA : Nat) (floor : Int)
    (best : Option Candidate) (r : Nat) (c : Candidate) (floorRange : Int53.InRange floor)
    (frame : Frame s heap0 refs cA fA bA floor best) (member : r ∈ refs) (at_ : CandidateAt heap0 r c) :
    WPS P (s.declare "candidate" (.ref r)) loopBody (fun out => out.control = .normal ∧
      Frame { out.state with env := s.env } heap0 refs cA fA bA floor (pick floor best c)) := by
  obtain ⟨o1, o2, o3, o4⟩ := frame.order
  have henv := frame.env
  obtain ⟨hfA, fCell⟩ := getElem_of_some frame.floorCell
  obtain ⟨bv, bCell, bRel⟩ := frame.bestCell
  obtain ⟨hbA, bCell'⟩ := getElem_of_some bCell
  have hb1 : bA < s.heap.length + 1 := by omega
  conv => arg 3; simp only [loopBody, chooseFn, P, Extracted_reference_decision.program, List.getElem!_cons_zero]
  cases c with
  | rejected c =>
    obtain ⟨fields, rec, kind, reason⟩ := at_
    have hr : r < heap0.length := (List.getElem?_eq_some_iff.mp rec).choose
    have rec' : s.heap[r]? = some (.record fields) := (frame.inputs r hr).trans rec
    obtain ⟨hrs, rec''⟩ := getElem_of_some rec'
    wp
    refine ⟨trivial, ?_⟩
    have same : pick floor best (.rejected c) = best := rfl
    rw [same, ← henv]
    exact frame.append _
  | valid c =>
    obtain ⟨fields, rec, kind, version, ident, range⟩ := at_
    have hr : r < heap0.length := (List.getElem?_eq_some_iff.mp rec).choose
    have rec' : s.heap[r]? = some (.record fields) := (frame.inputs r hr).trans rec
    obtain ⟨hrs, rec''⟩ := getElem_of_some rec'
    have floorCompare := Int53.le_ofInt floor c.version floorRange range
    by_cases above : floor ≤ c.version
    · cases best with
      | none =>
        simp only [BestAt] at bRel
        subst bRel
        wp
        refine ⟨trivial, ?_⟩
        have chosen : pick floor none (.valid c) = some (.valid c) := by simp [pick, above]
        rw [chosen, ← henv]
        exact frame.rebind' _ _ _ ⟨r, rfl, member, ⟨fields, rec, kind, version, ident, range⟩, c, rfl⟩
      | some previous =>
        obtain ⟨pa, rfl, pmem, pat, pv, rfl⟩ := bRel
        obtain ⟨pfields, prec, pkind, pversion, pident, prange⟩ := pat
        have hpa : pa < heap0.length := (List.getElem?_eq_some_iff.mp prec).choose
        have prec' : s.heap[pa]? = some (.record pfields) := (frame.inputs pa hpa).trans prec
        obtain ⟨hpas, prec''⟩ := getElem_of_some prec'
        have lt := Int53.lt_ofInt pv.version c.version prange range
        have eq := Int53.beq_ofInt c.version pv.version range prange
        have swap : compare c.id pv.id = (compare pv.id c.id).swap := Std.OrientedOrd.eq_swap
        have candidateAt : CandidateAt heap0 r (.valid c) := ⟨fields, rec, kind, version, ident, range⟩
        by_cases newer : pv.version < c.version
        · clear swap
          wp
          refine ⟨trivial, ?_⟩
          have e : pick floor (some (.valid pv)) (.valid c) = some (.valid c) := by simp [pick, above, newer]
          rw [e, ← henv]
          exact frame.rebind' _ _ _ ⟨r, rfl, member, candidateAt, c, rfl⟩
        · by_cases same : c.version = pv.version
          · cases hcmp : compare pv.id c.id
            · have flipped : compare c.id pv.id = .gt := by rw [swap, hcmp]; rfl
              have e : pick floor (some (.valid pv)) (.valid c) = some (.valid c) := by
                unfold pick; dsimp only; rw [if_pos above]; simp [newer, same, hcmp]
              have sameB : (c.version == pv.version) = true := by simp [same]
              clear swap same
              wp
              refine ⟨trivial, ?_⟩
              rw [← henv]
              exact frame.rebind' _ _ _ ⟨r, rfl, member, candidateAt, c, rfl⟩
            · have flipped : compare c.id pv.id = .eq := by rw [swap, hcmp]; rfl
              have e : pick floor (some (.valid pv)) (.valid c) = some (.valid pv) := by
                unfold pick; dsimp only; rw [if_pos above]; simp [newer, same, hcmp]
              have sameB : (c.version == pv.version) = true := by simp [same]
              clear swap same
              wp
              refine ⟨trivial, ?_⟩
              rw [← henv]
              exact frame.append _
            · have flipped : compare c.id pv.id = .lt := by rw [swap, hcmp]; rfl
              have e : pick floor (some (.valid pv)) (.valid c) = some (.valid pv) := by
                unfold pick; dsimp only; rw [if_pos above]; simp [newer, same, hcmp]
              have sameB : (c.version == pv.version) = true := by simp [same]
              clear swap same
              wp
              refine ⟨trivial, ?_⟩
              rw [← henv]
              exact frame.append _
          · have e : pick floor (some (.valid pv)) (.valid c) = some (.valid pv) := by
              simp [pick, above, newer, same]
            have sameB : (c.version == pv.version) = false := by simp [same]
            clear swap
            wp
            refine ⟨trivial, ?_⟩
            rw [← henv]
            exact frame.append _
    · cases best with
      | none =>
        simp only [BestAt] at bRel
        subst bRel
        wp
        refine ⟨trivial, ?_⟩
        have kept : pick floor none (.valid c) = none := by simp [pick, above]
        rw [kept, ← henv]
        exact frame.append _
      | some previous =>
        obtain ⟨pa, rfl, pmem, pat, pv, rfl⟩ := bRel
        wp
        refine ⟨trivial, ?_⟩
        have kept : pick floor (some (.valid pv)) (.valid c) = some (.valid pv) := by simp [pick, above]
        rw [kept, ← henv]
        exact frame.append _

theorem loop (heap0 : Heap) (refs : List Nat) (cA fA bA : Nat) (floor : Int) (floorRange : Int53.InRange floor)
    {rest : List Nat} {natives : List Candidate} (elements : Elementwise (CandidateAt heap0) rest natives) :
    ∀ (s : State) (best : Option Candidate), (∀ r ∈ rest, r ∈ refs) →
      Frame s heap0 refs cA fA bA floor best →
      WPEach P s "candidate" loopBody (rest.map .ref) (fun out => out.control = .normal ∧
        Frame out.state heap0 refs cA fA bA floor (natives.foldl (pick floor) best)) := by
  induction elements with
  | nil => intro s best _ frame; exact WPEach.nil ⟨rfl, frame⟩
  | @cons r c rest natives head _ ih =>
    intro s best sub frame
    refine WPEach.cons ((iteration s heap0 refs cA fA bA floor best r c floorRange frame (sub r (by simp)) head).mono ?_)
    rintro out ⟨normal, next⟩
    simp only [normal, reduceCtorEq, ↓reduceIte]
    exact ih _ _ (fun x member => sub x (List.mem_cons_of_mem _ member)) next

theorem iterable_array {s : State} {l : Nat} {xs : List Value} (h : s.heap[l]? = some (.array xs)) :
    iterable s (.ref l) = .ok (xs, s) := by
  simp [iterable, h, pure, Except.pure]

/-- `choose`, run by the original evaluator on an array of candidate records,
returns `undefined` exactly when the emitted `choose` returns `none`; otherwise
it returns one of the input records, which represents the emitted result. -/
theorem choose_source (before : State) (array : Nat) (refs : List Nat) (natives : List Candidate) (floor : Int)
    (floorRange : Int53.InRange floor) (arrayAt : before.heap[array]? = some (.array (refs.map .ref)))
    (elements : Elementwise (CandidateAt before.heap) refs natives) :
    WPI P before (.function "choose") [.ref array, .number (Float.Model.ofInt floor)] (fun result _ =>
      BestAt before.heap refs result («choose» natives floor)) := by
  rw [← chooseName]
  refine WPI.function chooseFind ?_
  obtain ⟨harray, arrayAt'⟩ := getElem_of_some arrayAt
  conv => arg 3; simp only [chooseFn, P, Extracted_reference_decision.program, List.getElem!_cons_zero]
  conv => arg 2; simp only [chooseFn, P, Extracted_reference_decision.program, List.getElem!_cons_zero]
  refine WPS.block ?_
  refine WPB.cons ?_
  refine WPS.let_ ?_
  refine WPE.literal ?_
  wp_reduce
  refine WPB.cons ?_
  refine WPS.forOf ?_
  refine WPE.var (by wp_eval) ?_
  refine ⟨_, _, iterable_array (by wp_eval), ?_⟩
  have start : Frame (((bindArguments before
      [{ name := "candidates", ty := (Ty.named "Candidate").array.readonly, span := { start := 262, stop := 272 } },
        { name := "floor", ty := Ty.named "Int53", span := { start := 296, stop := 301 } }]
      [Value.ref array, Value.number (Float.Model.ofInt floor)]).declare "best" Value.undefined))
      before.heap refs before.heap.length (before.heap.length + 1) (before.heap.length + 2) floor none := by
    refine ⟨by simp [bindArguments, State.declare, State.alloc], fun i hi => ?_, ⟨Nat.le_refl _, by omega, by omega, ?_⟩,
      ?_, ⟨.undefined, ?_, rfl⟩⟩
    all_goals simp [*, bindArguments, State.declare, State.alloc, List.getElem?_append]
  refine (loop before.heap refs _ _ _ floor floorRange elements _ none (fun r member => member) start).mono ?_
  rintro out ⟨normal, frame⟩
  simp only [normal, ↓reduceIte]
  obtain ⟨v, cell, rel⟩ := frame.bestCell
  have henv := frame.env
  wp
  exact ⟨by simp, by rw [choose_fold]; exact rel⟩

/-! ## The reference theorems, for the source -/

/-- A run of the source `choose` exists, and its result represents the emitted `choose`. -/
theorem choose_spec_source (before : State) (array : Nat) (refs : List Nat) (natives : List Candidate)
    (floor : Int) (floorRange : Int53.InRange floor) (arrayAt : before.heap[array]? = some (.array (refs.map .ref)))
    (elements : Elementwise (CandidateAt before.heap) refs natives) :
    ∃ result after, SourceInvokes Extracted_reference_decision.source before (.function "choose")
      [.ref array, .number (Float.Model.ofInt floor)] result after ∧
      BestAt before.heap refs result («choose» natives floor) := by
  obtain ⟨result, after, invoked, rel⟩ := (choose_source before array refs natives floor floorRange arrayAt elements).elim
  exact ⟨result, after, Extracted_reference_decision.certificate.transfer_invocation invoked, rel⟩

/-- **The result is one of the inputs, or nothing, and never below the floor.**
Every run of the source `choose` returns `undefined` or the reference of one of the
input records; a returned record is a valid candidate whose version is at least the floor. -/
theorem choose_result_source (before : State) (array : Nat) (refs : List Nat) (natives : List Candidate)
    (floor : Int) (floorRange : Int53.InRange floor) (arrayAt : before.heap[array]? = some (.array (refs.map .ref)))
    (elements : Elementwise (CandidateAt before.heap) refs natives) {result : Value} {after : State}
    (run : SourceInvokes Extracted_reference_decision.source before (.function "choose")
      [.ref array, .number (Float.Model.ofInt floor)] result after) :
    result = .undefined ∨ ∃ address ∈ refs, result = .ref address ∧
      ∃ c, CandidateAt before.heap address (.valid c) ∧ floor ≤ c.version := by
  obtain ⟨v, after', spec, rel⟩ := choose_spec_source before array refs natives floor floorRange arrayAt elements
  obtain ⟨rfl, _⟩ := run.deterministic spec
  cases chosen : «choose» natives floor with
  | none => rw [chosen] at rel; exact Or.inl rel
  | some c =>
    rw [chosen] at rel
    obtain ⟨address, rfl, member, at_, valid, rfl⟩ := rel
    exact Or.inr ⟨address, member, rfl, valid, at_, Examples.Proofs.ReferenceDecision.choose_floor chosen⟩

/-- **Permutation invariance.** Two arrays holding the same candidates in any
order make the source `choose` return records representing the same candidate. -/
theorem choose_permutation_source (beforeX beforeY : State) (arrayX arrayY : Nat) (refsX refsY : List Nat)
    (nativesX nativesY : List Candidate) (permutation : nativesX.Perm nativesY)
    (floor : Int) (floorRange : Int53.InRange floor)
    (arrayAtX : beforeX.heap[arrayX]? = some (.array (refsX.map .ref)))
    (arrayAtY : beforeY.heap[arrayY]? = some (.array (refsY.map .ref)))
    (elementsX : Elementwise (CandidateAt beforeX.heap) refsX nativesX)
    (elementsY : Elementwise (CandidateAt beforeY.heap) refsY nativesY)
    {resultX resultY : Value} {afterX afterY : State}
    (runX : SourceInvokes Extracted_reference_decision.source beforeX (.function "choose")
      [.ref arrayX, .number (Float.Model.ofInt floor)] resultX afterX)
    (runY : SourceInvokes Extracted_reference_decision.source beforeY (.function "choose")
      [.ref arrayY, .number (Float.Model.ofInt floor)] resultY afterY) :
    (resultX = .undefined ∧ resultY = .undefined) ∨
      ∃ x y c, resultX = .ref x ∧ resultY = .ref y ∧
        CandidateAt beforeX.heap x c ∧ CandidateAt beforeY.heap y c := by
  obtain ⟨vX, _, specX, relX⟩ := choose_spec_source beforeX arrayX refsX nativesX floor floorRange arrayAtX elementsX
  obtain ⟨vY, _, specY, relY⟩ := choose_spec_source beforeY arrayY refsY nativesY floor floorRange arrayAtY elementsY
  obtain ⟨rfl, _⟩ := runX.deterministic specX
  obtain ⟨rfl, _⟩ := runY.deterministic specY
  rw [Examples.Proofs.ReferenceDecision.choose_permutation permutation floor] at relX
  cases chosen : «choose» nativesY floor with
  | none => rw [chosen] at relX relY; exact Or.inl ⟨relX, relY⟩
  | some c =>
    rw [chosen] at relX relY
    obtain ⟨x, rfl, _, atX, _⟩ := relX
    obtain ⟨y, rfl, _, atY, _⟩ := relY
    exact Or.inr ⟨x, y, c, rfl, rfl, atX, atY⟩

end Examples.ReferenceSource.Decision
