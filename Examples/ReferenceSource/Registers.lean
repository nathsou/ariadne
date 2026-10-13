import Examples.ShallowReference.registers
import Ariadne.Shallow.Adequacy.WP
import Ariadne.Shallow.Adequacy.ScalarMap
import Ariadne.Shallow.Adequacy.ClassConstruction
import Ariadne.SourceTrace
import Examples.Proofs.ReferenceRegisters

/-!
# The register store, transferred to its TypeScript source

Every method of `examples/reference/registers.ts`, run by the original evaluator
on any heap that represents a native state, returns what the emitted Lean method
returns and leaves a heap that represents the emitted method's new state.
-/

namespace Examples.ReferenceSource.Registers
open Ariadne Ariadne.Shallow Ariadne.Shallow.Adequacy Extracted_reference_registers.Shallow
open Heap

abbrev P := Extracted_reference_registers.program
abbrev State' := NativeTypes.«Registers#state»

def stringInts : List (JSString × Int) → List (Value × Value) :=
  encodeEntries .string (fun n => .number (Float.Model.ofInt n))
def stringStrings : List (JSString × JSString) → List (Value × Value) :=
  encodeEntries .string .string

/-- The heap shape of a register store: an instance whose three private fields
reference three distinct maps holding the encoded native entries. -/
structure Layout (heap : Heap) (address : Nat) (native : State') (fields : List (String × Value))
    (values stamps counters : Nat) : Prop where
  instance_ : heap[address]? = some (.instance_ "Registers" fields)
  valuesField : fields.lookup "values" = some (.ref values)
  stampsField : fields.lookup "stamps" = some (.ref stamps)
  countersField : fields.lookup "counters" = some (.ref counters)
  valuesMap : heap[values]? = some (.map (stringInts native.values.entries))
  stampsMap : heap[stamps]? = some (.map (stringStrings native.stamps.entries))
  countersMap : heap[counters]? = some (.map (stringInts native.counters.entries))
  valuesRange : ∀ entry ∈ native.values.entries, Int53.InRange entry.2
  countersRange : ∀ entry ∈ native.counters.entries, Int53.InRange entry.2
  distinct : values ≠ stamps ∧ values ≠ counters ∧ stamps ≠ counters ∧
    address ≠ values ∧ address ≠ stamps ∧ address ≠ counters

/-- The representation relation used by the generated wrappers and theorems. -/
def layout : DataRelation Value State' :=
  ((DataRelation.field "values" (DataRelation.map DataRelation.string DataRelation.int53)
    (DataRelation.field "stamps" (DataRelation.map DataRelation.string DataRelation.string)
      (DataRelation.field "counters" (DataRelation.map DataRelation.string DataRelation.int53)
        DataRelation.fieldsNil))).classState "Registers").comap NativeDestruct.«Registers#state»

private theorem stringInts_holds {heap : Heap} {source : Value} {native : JSMap JSString Int} {footprint : Footprint} :
    (DataRelation.map DataRelation.string DataRelation.int53).Holds heap source native footprint ↔
      ∃ address, source = .ref address ∧ heap[address]? = some (.map (stringInts native.entries)) ∧
        (∀ entry ∈ native.entries, Int53.InRange entry.2) ∧ footprint = [address] := by
  have := map_scalar_iff (heap := heap) (source := source) (native := native) (footprint := footprint)
    ScalarCodec.string ScalarCodec.int53
  simp only [ScalarCodec.string, ScalarCodec.int53, true_and] at this
  exact this

private theorem stringStrings_holds {heap : Heap} {source : Value} {native : JSMap JSString JSString}
    {footprint : Footprint} :
    (DataRelation.map DataRelation.string DataRelation.string).Holds heap source native footprint ↔
      ∃ address, source = .ref address ∧ heap[address]? = some (.map (stringStrings native.entries)) ∧
        footprint = [address] := by
  have := map_scalar_iff (heap := heap) (source := source) (native := native) (footprint := footprint)
    ScalarCodec.string ScalarCodec.string
  simp only [ScalarCodec.string, and_self, implies_true, true_and] at this
  exact this

/-- The relation is exactly the concrete layout, owning the instance and its three maps. -/
theorem layout_iff {heap : Heap} {address : Nat} {native : State'} {owned : Footprint} :
    layout.Holds heap (.ref address) native owned ↔
      ∃ fields values stamps counters, Layout heap address native fields values stamps counters ∧
        owned = [address, values, stamps, counters] := by
  constructor
  · rintro ⟨root, object, children, same, lookup, ⟨fields, project, related⟩, fresh, rfl⟩
    cases same
    cases object
    all_goals try simp at project
    case instance_ name actual =>
      obtain ⟨rfl, rfl⟩ := project
      obtain ⟨vv, vLookup, fv, rest, vHolds, restHolds, vSep, rfl⟩ := related
      obtain ⟨sv, sLookup, fs, rest', sHolds, rest'Holds, sSep, rfl⟩ := restHolds
      obtain ⟨cv, cLookup, fc, nil, cHolds, nilHolds, cSep, rfl⟩ := rest'Holds
      obtain ⟨vA, rfl, vMap, vRange, rfl⟩ := stringInts_holds.mp vHolds
      obtain ⟨sA, rfl, sMap, rfl⟩ := stringStrings_holds.mp sHolds
      obtain ⟨cA, rfl, cMap, cRange, rfl⟩ := stringInts_holds.mp cHolds
      obtain ⟨_, rfl⟩ := nilHolds
      simp only [Disjoint, List.mem_singleton, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq, List.cons_append, List.nil_append, List.append_nil] at vSep sSep cSep fresh
      refine ⟨actual, vA, sA, cA, ⟨lookup, vLookup, sLookup, cLookup, vMap, sMap, cMap, vRange, cRange, ?_⟩, rfl⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | (intro h; subst h; simp_all)
        | simp_all
  · rintro ⟨fields, vA, sA, cA, l, rfl⟩
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := l.distinct
    refine ⟨address, .instance_ "Registers" fields, [vA] ++ ([sA] ++ ([cA] ++ [])), rfl, l.instance_,
      ⟨fields, by simp, ?_⟩, ?_, by simp⟩
    · refine ⟨_, l.valuesField, [vA], [sA] ++ ([cA] ++ []), stringInts_holds.mpr ⟨vA, rfl, l.valuesMap, l.valuesRange, rfl⟩,
        ⟨_, l.stampsField, [sA], [cA] ++ [], stringStrings_holds.mpr ⟨sA, rfl, l.stampsMap, rfl⟩,
          ⟨_, l.countersField, [cA], [], stringInts_holds.mpr ⟨cA, rfl, l.countersMap, l.countersRange, rfl⟩,
            ⟨trivial, rfl⟩, by simp [Disjoint], rfl⟩, ?_, rfl⟩, ?_, rfl⟩
      · simp [Disjoint, d3]
      · simp [Disjoint, d1, d2]
    · simp [d4, d5, d6]

/-! ## Method bodies -/

theorem zero_literal : Value.ofLiteral (.number 0 0) = .number (Float.Model.ofInt 0) := by kernel_rfl
theorem zero_scientific : Float.Model.ofScientific 0 0 = Float.Model.ofInt 0 := by kernel_rfl

theorem mapSet_stringInts (xs : List (JSString × Int)) (k : JSString) (v : Int) :
    mapSet (stringInts xs) (.string k) (.number (Float.Model.ofInt v)) = stringInts (MapEntries.set xs k v) :=
  mapSet_string (fun n => .number (Float.Model.ofInt n)) xs k v

theorem mapSet_stringStrings (xs : List (JSString × JSString)) (k v : JSString) :
    mapSet (stringStrings xs) (.string k) (.string v) = stringStrings (MapEntries.set xs k v) :=
  mapSet_string .string xs k v

theorem mapGet_stringStrings (xs : List (JSString × JSString)) (k : JSString) :
    mapGet (stringStrings xs) (.string k) = ((MapEntries.get xs k).map .string).getD .undefined :=
  mapGet_string .string xs k

theorem mapGet_stringInts (xs : List (JSString × Int)) (k : JSString) :
    mapGet (stringInts xs) (.string k) =
      ((MapEntries.get xs k).map fun n => Value.number (Float.Model.ofInt n)).getD .undefined :=
  mapGet_string _ xs k



def regClass : Ariadne.Class := P.classes[0]!
theorem regFind : P.classes.find? (·.name == regClass.name) = some regClass := by kernel_rfl
theorem regName : regClass.name = "Registers" := by kernel_rfl

def method (index : Nat) : Ariadne.Function := regClass.methods[index]!
theorem methodFind (index : Nat) (bound : index < 4 := by decide) :
    regClass.methods.find? (·.name == (method index).name) = some (method index) := by
  rcases index with _ | _ | _ | _ | index
  all_goals first | kernel_rfl | omega

/-- Lookup and operator side conditions of a concrete source body. -/
macro "wp_eval" : tactic => `(tactic| (simp +arith [*, Shallow.Adequacy.bindArguments, State.declare,
  State.alloc, State.lookup, State.assign, State.write, readMember, List.getElem?_append, List.getElem?_set,
  List.find?_cons, binary, unary, Value.ofLiteral, strictEqual, Value.truthy, zero_literal, zero_scientific, mapGet_stringInts, mapGet_stringStrings, mapSet_stringInts,
  mapSet_stringStrings,
  pure, Except.pure, bind, Except.bind]; try rfl))

/-- One weakest-precondition step for the node at the head of the goal. -/
macro "wp_step" : tactic => `(tactic| first
  | refine WPS.block ?_
  | refine WPB.nil ?_
  | refine WPB.cons ?_
  | refine WPS.return_ ?_
  | refine WPS.let_ ?_
  | refine WPS.expr ?_
  | refine WPS.if_ ?_
  | refine WPS.assignVar ?_
  | refine WPE.literal ?_
  | refine WPE.var (by wp_eval) ?_
  | refine WPE.call ?_
  | refine WPE.member ?_
  | refine WPE.and ?_
  | refine WPE.or ?_
  | refine WPE.coalesce ?_
  | refine WPE.binary (by decide) ?_
  | refine WPE.unary ?_
  | refine WPA.nil ?_
  | refine WPA.cons ?_
  | refine WPI.map_get (by wp_eval) ?_
  | refine WPI.map_has (by wp_eval) ?_
  | refine WPI.map_set (by wp_eval) ?_
  | refine WPI.map_delete (by wp_eval) ?_
  | refine ⟨_, by wp_eval, ?_⟩
  | (rw [if_pos (by assumption)])
  | (rw [if_neg (by assumption)])
  | (simp only [*, Value.truthy, strictEqual, zero_literal, zero_scientific, decide_true, decide_false, gt_iff_lt, mapGet_stringInts, mapGet_stringStrings, Option.map_none, Option.map_some,
      Option.getD_none, Option.getD_some, ↓reduceIte, reduceCtorEq, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      bne_iff_ne, ne_eq, bne_self_eq_false, not_true_eq_false, not_false_eq_true]))

macro "wp" : tactic => `(tactic| repeat wp_step)

/-- Unfold a method of the class into its literal body and parameters. -/
macro "unfold_method" : tactic => `(tactic| (
  conv => arg 3; simp only [method, regClass, P, Extracted_reference_registers.program,
    List.getElem!_cons_zero, List.getElem!_cons_succ]
  conv => arg 2; simp only [method, regClass, P, Extracted_reference_registers.program,
    List.getElem!_cons_zero, List.getElem!_cons_succ]))

theorem getElem_of_some {heap : Heap} {i : Nat} {o : Object} (h : heap[i]? = some o) :
    ∃ bound : i < heap.length, heap[i] = o :=
  ⟨(List.getElem?_eq_some_iff.mp h).choose, (List.getElem?_eq_some_iff.mp h).choose_spec⟩

/-- Heaps that keep every existing object keep the layout. -/
theorem Layout.extend {heap : Heap} {address : Nat} {native : State'} {fields : List (String × Value)}
    {vA sA cA : Nat} (l : Layout heap address native fields vA sA cA) (heap' : Heap)
    (agree : ∀ i, i < heap.length → heap'[i]? = heap[i]?) : Layout heap' address native fields vA sA cA := by
  have bound {i : Nat} {o : Object} (h : heap[i]? = some o) : i < heap.length :=
    (List.getElem?_eq_some_iff.mp h).choose
  exact ⟨(agree _ (bound l.instance_)).trans l.instance_, l.valuesField, l.stampsField, l.countersField,
    (agree _ (bound l.valuesMap)).trans l.valuesMap, (agree _ (bound l.stampsMap)).trans l.stampsMap,
    (agree _ (bound l.countersMap)).trans l.countersMap, l.valuesRange, l.countersRange, l.distinct⟩

theorem bindArguments_agree (state : State) (params : List Param) (args : List Value) :
    ∀ i, i < state.heap.length → (bindArguments state params args).heap[i]? = state.heap[i]? := by
  unfold bindArguments
  generalize hs : ({ state with env := [] } : State) = start
  have same : start.heap = state.heap := by rw [← hs]
  rw [← same]
  clear hs same
  induction params generalizing args start with
  | nil => intro i _; simp
  | cons p ps ih =>
    cases args with
    | nil => intro i _; simp
    | cons v vs =>
      intro i hi
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [ih vs (start.declare p.name v) i (by simp [State.declare, State.alloc]; omega)]
      simp [State.declare, State.alloc, List.getElem?_append_left hi]

theorem read_source (before : State) (address : Nat) (native : State') (fields : List (String × Value))
    (vA sA cA : Nat) (a b : JSString) (input : Layout before.heap address native fields vA sA cA) :
    WPI P before (.method address "read") [.string a, .string b] (fun result after =>
      result = ((«Registers#read» native a b).map fun n => Value.number (Float.Model.ofInt n)).getD .undefined ∧
      Layout after.heap address native fields vA sA cA) := by
  obtain ⟨ha, inst⟩ := getElem_of_some input.instance_
  obtain ⟨hv, vMap⟩ := getElem_of_some input.valuesMap
  have fv := input.valuesField
  change WPI P before (.method address (method 1).name) _ _
  refine WPI.method (class_ := regClass) (by rw [regName]; exact input.instance_) regFind (methodFind 1) ?_
  unfold_method
  wp
  refine ⟨by simp, ?_, input.extend _ (bindArguments_agree _ _ _)⟩
  simp [«Registers#read», JSMap.get, stringInts, mapGet_string, NativeDestruct.«Registers#state»]

theorem MapEntries.snd_mem_set (xs : List (JSString × Int)) (k : JSString) (v : Int) :
    ∀ e ∈ MapEntries.set xs k v, e.2 = v ∨ e ∈ xs := by
  induction xs with
  | nil => simp [MapEntries.set]
  | cons entry xs ih =>
    rcases entry with ⟨k', v'⟩
    intro e member
    simp only [MapEntries.set] at member
    split at member
    · rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ member)
    · rcases List.mem_cons.mp member with rfl | member
      · exact Or.inr (List.mem_cons_self ..)
      · rcases ih e member with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem range_set {xs : List (JSString × Int)} (valid : ∀ e ∈ xs, Int53.InRange e.2) (k : JSString) {v : Int}
    (range : Int53.InRange v) : ∀ e ∈ MapEntries.set xs k v, Int53.InRange e.2 := by
  intro e member
  rcases MapEntries.snd_mem_set xs k v e member with h | h
  · rw [h]; exact range
  · exact valid e h

/-- Rewriting the three maps in place, and nothing else, re-establishes the layout. -/
theorem Layout.update {heap heap' : Heap} {address : Nat} {native : State'} {fields : List (String × Value)}
    {vA sA cA : Nat} (l : Layout heap address native fields vA sA cA) (native' : State')
    (agree : ∀ i, i < heap.length → vA ≠ i → sA ≠ i → cA ≠ i → heap'[i]? = heap[i]?)
    (values : heap'[vA]? = some (.map (stringInts native'.values.entries)))
    (stamps : heap'[sA]? = some (.map (stringStrings native'.stamps.entries)))
    (counters : heap'[cA]? = some (.map (stringInts native'.counters.entries)))
    (valuesRange : ∀ e ∈ native'.values.entries, Int53.InRange e.2)
    (countersRange : ∀ e ∈ native'.counters.entries, Int53.InRange e.2) :
    Layout heap' address native' fields vA sA cA := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := l.distinct
  have bound : address < heap.length := (List.getElem?_eq_some_iff.mp l.instance_).choose
  exact ⟨(agree address bound (Ne.symm d4) (Ne.symm d5) (Ne.symm d6)).trans l.instance_, l.valuesField,
    l.stampsField, l.countersField, values, stamps, counters, valuesRange, countersRange, l.distinct⟩

set_option hygiene false in
/-- Name every fact of the input layout for the evaluation steps. -/
macro "layout_facts" : tactic => `(tactic| (
  obtain ⟨ha, inst⟩ := getElem_of_some input.instance_
  obtain ⟨hv, vMap⟩ := getElem_of_some input.valuesMap
  obtain ⟨hs, sMap⟩ := getElem_of_some input.stampsMap
  obtain ⟨hcA, cMap⟩ := getElem_of_some input.countersMap
  have fv := input.valuesField
  have fs := input.stampsField
  have fc := input.countersField
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := input.distinct
  have e1 := Ne.symm d1; have e2 := Ne.symm d2; have e3 := Ne.symm d3
  have e4 := Ne.symm d4; have e5 := Ne.symm d5; have e6 := Ne.symm d6))

set_option hygiene false in
/-- Shared closing step: the final heap only rewrote the selected maps. -/
macro "layout_close" : tactic => `(tactic| (
  refine ⟨by simp, by first | rfl | simp, ?_⟩
  refine Layout.update input _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi n1 n2 n3
    simp [*, List.getElem?_set, List.getElem?_append, Shallow.Adequacy.bindArguments, State.declare, State.alloc]
  all_goals simp [*, List.getElem?_set, List.getElem?_append, Shallow.Adequacy.bindArguments, State.declare,
    State.alloc, «Registers#write», «Registers#count», zero_literal, zero_scientific, JSMap.set, JSMap.get, mapSet_stringInts, mapSet_stringStrings,
    NativeDestruct.«Registers#state», NativeConstruct.«Registers#state»]
  all_goals first
    | exact input.valuesRange
    | exact input.countersRange
    | exact range_set input.valuesRange _ range
    | exact range_set input.countersRange _ range
    | exact fun k v h => input.valuesRange (k, v) h
    | exact fun k v h => input.countersRange (k, v) h
    | exact fun k v h => range_set input.valuesRange _ range (k, v) h
    | exact fun k v h => range_set input.countersRange _ range (k, v) h))

theorem write_source (before : State) (address : Nat) (native : State') (fields : List (String × Value))
    (vA sA cA : Nat) (a b : JSString) (value : Int) (stamp : JSString) (range : Int53.InRange value)
    (input : Layout before.heap address native fields vA sA cA) :
    WPI P before (.method address "write")
      [.string a, .string b, .number (Float.Model.ofInt value), .string stamp] (fun result after =>
      result = .undefined ∧
      Layout after.heap address («Registers#write» native a b value stamp).2.1 fields vA sA cA) := by
  layout_facts
  change WPI P before (.method address (method 0).name) _ _
  refine WPI.method (class_ := regClass) (by rw [regName]; exact input.instance_) regFind (methodFind 0) ?_
  unfold_method
  cases seen : MapEntries.get native.stamps.entries (a ++ 0 :: b) with
  | none =>
    wp
    layout_close
  | some old =>
    by_cases hc : compare old stamp = Ordering.lt
    · wp
      have swap : compare stamp old = .gt := by rw [Std.OrientedOrd.eq_swap, hc]; rfl
      layout_close
    · wp
      have swap : compare stamp old ≠ .gt := by
        rw [Std.OrientedOrd.eq_swap]; cases h : compare old stamp <;> simp_all [Ordering.swap]
      layout_close

theorem range_get {xs : List (JSString × Int)} (valid : ∀ e ∈ xs, Int53.InRange e.2) {k : JSString} {v : Int}
    (found : MapEntries.get xs k = some v) : Int53.InRange v := by
  induction xs with
  | nil => simp [MapEntries.get] at found
  | cons entry xs ih =>
    rcases entry with ⟨k', v'⟩
    simp only [MapEntries.get] at found
    split at found
    · cases found; exact valid (k', v) (List.mem_cons_self ..)
    · exact ih (fun e member => valid e (List.mem_cons_of_mem _ member)) found

theorem count_source (before : State) (address : Nat) (native : State') (fields : List (String × Value))
    (vA sA cA : Nat) (key replica : JSString) (value : Int) (range : Int53.InRange value)
    (input : Layout before.heap address native fields vA sA cA) :
    WPI P before (.method address "count") [.string key, .string replica, .number (Float.Model.ofInt value)]
      (fun result after => result = .undefined ∧
        Layout after.heap address («Registers#count» native key replica value).2.1 fields vA sA cA) := by
  layout_facts
  change WPI P before (.method address (method 2).name) _ _
  refine WPI.method (class_ := regClass) (by rw [regName]; exact input.instance_) regFind (methodFind 2) ?_
  unfold_method
  cases seen : MapEntries.get native.counters.entries (key ++ 0 :: replica) with
  | none =>
    have compare := Int53.lt_ofInt 0 value Int53.zero_inRange range
    by_cases grows : 0 < value
    · wp
      layout_close
    · wp
      layout_close
  | some old =>
    have compare := Int53.lt_ofInt old value (range_get input.countersRange seen) range
    by_cases grows : old < value
    · wp
      layout_close
    · wp
      layout_close

theorem counter_source (before : State) (address : Nat) (native : State') (fields : List (String × Value))
    (vA sA cA : Nat) (key replica : JSString) (input : Layout before.heap address native fields vA sA cA) :
    WPI P before (.method address "counter") [.string key, .string replica] (fun result after =>
      result = .number (Float.Model.ofInt («Registers#counter» native key replica)) ∧
      Layout after.heap address native fields vA sA cA) := by
  layout_facts
  change WPI P before (.method address (method 3).name) _ _
  refine WPI.method (class_ := regClass) (by rw [regName]; exact input.instance_) regFind (methodFind 3) ?_
  unfold_method
  cases seen : MapEntries.get native.counters.entries (key ++ 0 :: replica) with
  | none =>
    wp
    refine ⟨by simp, ?_, input.extend _ (bindArguments_agree _ _ _)⟩
    simp [«Registers#counter», JSMap.get, NativeDestruct.«Registers#state», seen, zero_literal]
  | some old =>
    wp
    refine ⟨by simp, ?_, input.extend _ (bindArguments_agree _ _ _)⟩
    simp [«Registers#counter», JSMap.get, NativeDestruct.«Registers#state», seen]

/-! ## Construction and call traces -/

theorem regPlain : regClass.constructor_ = none := by kernel_rfl

/-- `new Registers()` allocates three empty maps and then the instance. -/
theorem new_source (before : State) (span : Span) :
    let n := before.heap.length
    ∃ after, SourceEvaluates Extracted_reference_registers.source before (.newClass "Registers" [] span)
      (.ref (n + 3)) after ∧
      Layout after.heap (n + 3) «Registers##new» [("values", .ref n), ("stamps", .ref (n + 1)), ("counters", .ref (n + 2))]
        n (n + 1) (n + 2) := by
  intro n
  have initializers : EvaluatesFields P before (regClass.fields.map fun f => (f.name, f.value)) []
      [("values", .ref n), ("stamps", .ref (n + 1)), ("counters", .ref (n + 2))]
      (((before.alloc (.map [])).2.alloc (.map [])).2.alloc (.map [])).2 := by
    simp only [regClass, P, Extracted_reference_registers.program, List.getElem!_cons_zero, List.map_cons,
      List.map_nil]
    refine EvaluatesFields.cons (Evaluates.newMap _ _ _ _ _) ?_ (by decide)
    refine EvaluatesFields.cons (Evaluates.newMap _ _ _ _ _) ?_ (by decide)
    refine EvaluatesFields.cons (Evaluates.newMap _ _ _ _ _) ?_ (by decide)
    simp only [State.alloc, List.length_append, List.length_cons, List.length_nil, fieldSet, n]
    exact EvaluatesFields.nil _ _ _
  have evaluated := Evaluates.newClass_plain regFind regPlain (EvaluatesArgs.nil P before) initializers span
  rw [regName] at evaluated
  have length : (((before.alloc (.map [])).2.alloc (.map [])).2.alloc (.map [])).2.heap.length = n + 3 := by
    simp [State.alloc, n]
  rw [length] at evaluated
  refine ⟨_, Extracted_reference_registers.certificate.transfer_evaluation evaluated, ?_⟩
  · refine ⟨?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [State.alloc, n, List.getElem?_append, «Registers##new», JSMap.empty, stringInts, stringStrings,
      encodeEntries]

/-- The source call each native operation stands for. -/
def call (address : Nat) : Examples.Proofs.ReferenceRegisters.Operation → Value × List Value
  | .write a b v t => (.method address "write", [.string a, .string b, .number (Float.Model.ofInt v), .string t])
  | .count a b v => (.method address "count", [.string a, .string b, .number (Float.Model.ofInt v)])

/-- Source values are safe integers (the `Int53` refinement of the parameters). -/
def Valid : Examples.Proofs.ReferenceRegisters.Operation → Prop
  | .write _ _ v _ | .count _ _ v => Int53.InRange v

theorem operation_source (before : State) (address : Nat) (native : State') (fields : List (String × Value))
    (vA sA cA : Nat) (op : Examples.Proofs.ReferenceRegisters.Operation) (valid : Valid op)
    (input : Layout before.heap address native fields vA sA cA) :
    ∃ after, SourceInvokes Extracted_reference_registers.source before (call address op).1 (call address op).2
      .undefined after ∧
      Layout after.heap address (Examples.Proofs.ReferenceRegisters.applyOp native op) fields vA sA cA := by
  cases op with
  | write a b v t =>
    obtain ⟨result, after, invoked, rfl, layout⟩ := (write_source before address native fields vA sA cA a b v t valid input).elim
    exact ⟨after, Extracted_reference_registers.certificate.transfer_invocation invoked, layout⟩
  | count a b v =>
    obtain ⟨result, after, invoked, rfl, layout⟩ := (count_source before address native fields vA sA cA a b v valid input).elim
    exact ⟨after, Extracted_reference_registers.certificate.transfer_invocation invoked, layout⟩

/-- Any sequence of valid operations, run by the original evaluator, keeps
the instance representing the emitted state after the same operations. -/
theorem trace_source (before : State) (address : Nat) (native : State') (fields : List (String × Value))
    (vA sA cA : Nat) (ops : List Examples.Proofs.ReferenceRegisters.Operation) (valid : ∀ op ∈ ops, Valid op)
    (input : Layout before.heap address native fields vA sA cA) :
    ∃ after, SourceTrace Extracted_reference_registers.source before (ops.map (call address))
      (ops.map fun _ => .undefined) after ∧
      Layout after.heap address (ops.foldl Examples.Proofs.ReferenceRegisters.applyOp native) fields vA sA cA := by
  induction ops generalizing before native with
  | nil => exact ⟨before, .nil before, input⟩
  | cons op ops ih =>
    obtain ⟨middle, invoked, layout⟩ := operation_source before address native fields vA sA cA op
      (valid op (List.mem_cons_self ..)) input
    obtain ⟨after, rest, final⟩ := ih middle _ (fun op member => valid op (List.mem_cons_of_mem _ member)) layout
    exact ⟨after, .next invoked rest, final⟩

/-- Reading after the trace observes the emitted read of the final state. -/
theorem trace_read_source (before : State) (address : Nat) (native : State') (fields : List (String × Value))
    (vA sA cA : Nat) (ops : List Examples.Proofs.ReferenceRegisters.Operation) (valid : ∀ op ∈ ops, Valid op)
    (input : Layout before.heap address native fields vA sA cA) (a b : JSString) :
    ∃ after, SourceTrace Extracted_reference_registers.source before
      (ops.map (call address) ++ [(.method address "read", [.string a, .string b])])
      (ops.map (fun _ => .undefined) ++
        [((«Registers#read» (ops.foldl Examples.Proofs.ReferenceRegisters.applyOp native) a b).map
          fun n => Value.number (Float.Model.ofInt n)).getD .undefined]) after := by
  obtain ⟨middle, trace, layout⟩ := trace_source before address native fields vA sA cA ops valid input
  obtain ⟨result, after, invoked, rfl, _⟩ := (read_source middle address _ fields vA sA cA a b layout).elim
  exact ⟨after, trace.append (.next (Extracted_reference_registers.certificate.transfer_invocation invoked) (.nil _))⟩

theorem trace_counter_source (before : State) (address : Nat) (native : State') (fields : List (String × Value))
    (vA sA cA : Nat) (ops : List Examples.Proofs.ReferenceRegisters.Operation) (valid : ∀ op ∈ ops, Valid op)
    (input : Layout before.heap address native fields vA sA cA) (a b : JSString) :
    ∃ after, SourceTrace Extracted_reference_registers.source before
      (ops.map (call address) ++ [(.method address "counter", [.string a, .string b])])
      (ops.map (fun _ => .undefined) ++
        [.number (Float.Model.ofInt («Registers#counter» (ops.foldl Examples.Proofs.ReferenceRegisters.applyOp native) a b))])
      after := by
  obtain ⟨middle, trace, layout⟩ := trace_source before address native fields vA sA cA ops valid input
  obtain ⟨result, after, invoked, rfl, _⟩ := (counter_source middle address _ fields vA sA cA a b layout).elim
  exact ⟨after, trace.append (.next (Extracted_reference_registers.certificate.transfer_invocation invoked) (.nil _))⟩

open Examples.Proofs.ReferenceRegisters in
/-- **Convergence, in the source.** On a fresh register store, any two orders of
the same compatible operations make a later `read` observe the same value. -/
theorem read_convergence_source (before : Ariadne.State) (span : Span) (xs ys : List Operation)
    (permutation : xs.Perm ys) (consistent : ∀ x ∈ xs, ∀ y ∈ xs, Compatible x y)
    (valid : ∀ op ∈ xs, Valid op) (a b : JSString) :
    let address := before.heap.length + 3
    ∃ fresh value afterX afterY,
      SourceEvaluates Extracted_reference_registers.source before (.newClass "Registers" [] span) (.ref address) fresh ∧
      SourceTrace Extracted_reference_registers.source fresh
        (xs.map (call address) ++ [(.method address "read", [.string a, .string b])])
        (xs.map (fun _ => .undefined) ++ [value]) afterX ∧
      SourceTrace Extracted_reference_registers.source fresh
        (ys.map (call address) ++ [(.method address "read", [.string a, .string b])])
        (ys.map (fun _ => .undefined) ++ [value]) afterY := by
  intro address
  obtain ⟨fresh, constructed, layout⟩ := new_source before span
  have validY : ∀ op ∈ ys, Valid op := fun op member => valid op (permutation.mem_iff.mpr member)
  obtain ⟨afterX, traceX⟩ := trace_read_source fresh address _ _ _ _ _ xs valid layout a b
  obtain ⟨afterY, traceY⟩ := trace_read_source fresh address _ _ _ _ _ ys validY layout a b
  rw [read_convergence xs ys permutation consistent] at traceX
  exact ⟨fresh, _, afterX, afterY, constructed, traceX, traceY⟩

open Examples.Proofs.ReferenceRegisters in
/-- Counter components converge the same way. -/
theorem counter_convergence_source (before : Ariadne.State) (span : Span) (xs ys : List Operation)
    (permutation : xs.Perm ys) (consistent : ∀ x ∈ xs, ∀ y ∈ xs, Compatible x y)
    (valid : ∀ op ∈ xs, Valid op) (a b : JSString) :
    let address := before.heap.length + 3
    ∃ fresh value afterX afterY,
      SourceEvaluates Extracted_reference_registers.source before (.newClass "Registers" [] span) (.ref address) fresh ∧
      SourceTrace Extracted_reference_registers.source fresh
        (xs.map (call address) ++ [(.method address "counter", [.string a, .string b])])
        (xs.map (fun _ => .undefined) ++ [value]) afterX ∧
      SourceTrace Extracted_reference_registers.source fresh
        (ys.map (call address) ++ [(.method address "counter", [.string a, .string b])])
        (ys.map (fun _ => .undefined) ++ [value]) afterY := by
  intro address
  obtain ⟨fresh, constructed, layout⟩ := new_source before span
  have validY : ∀ op ∈ ys, Valid op := fun op member => valid op (permutation.mem_iff.mpr member)
  obtain ⟨afterX, traceX⟩ := trace_counter_source fresh address _ _ _ _ _ xs valid layout a b
  obtain ⟨afterY, traceY⟩ := trace_counter_source fresh address _ _ _ _ _ ys validY layout a b
  rw [counter_convergence xs ys permutation consistent] at traceX
  exact ⟨fresh, _, afterX, afterY, constructed, traceX, traceY⟩

open Examples.Proofs.ReferenceRegisters in
/-- **Idempotence, in the source.** Re-applying an operation leaves the instance
representing exactly the state it had after the first application, so no later
call can tell the two runs apart. -/
theorem idempotence_source (before : Ariadne.State) (address : Nat) (native : State') (fields : List (String × Value))
    (vA sA cA : Nat) (ops : List Operation) (op : Operation) (valid : ∀ x ∈ ops ++ [op], Valid x)
    (input : Layout before.heap address native fields vA sA cA) :
    ∃ once twice,
      SourceTrace Extracted_reference_registers.source before ((ops ++ [op]).map (call address))
        ((ops ++ [op]).map fun _ => .undefined) once ∧
      SourceTrace Extracted_reference_registers.source before ((ops ++ [op, op]).map (call address))
        ((ops ++ [op, op]).map fun _ => .undefined) twice ∧
      Layout once.heap address ((ops ++ [op]).foldl applyOp native) fields vA sA cA ∧
      Layout twice.heap address ((ops ++ [op]).foldl applyOp native) fields vA sA cA := by
  have validTwice : ∀ x ∈ ops ++ [op, op], Valid x := by
    intro x member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    exact valid x (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rcases member with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr h)
  obtain ⟨once, traceOnce, layoutOnce⟩ := trace_source before address native fields vA sA cA _ valid input
  obtain ⟨twice, traceTwice, layoutTwice⟩ := trace_source before address native fields vA sA cA _ validTwice input
  have same : (ops ++ [op, op]).foldl applyOp native = (ops ++ [op]).foldl applyOp native := by
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, idempotence]
  rw [same] at layoutTwice
  exact ⟨once, twice, traceOnce, traceTwice, layoutOnce, layoutTwice⟩

end Examples.ReferenceSource.Registers
