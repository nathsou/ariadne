import Ariadne.Shallow.Adequacy.ClassConstruction
import Examples.ClassAdequacy

namespace Examples.ClassAdequacy
open Ariadne Ariadne.Shallow Ariadne.Shallow.Adequacy Heap
open Extracted_classes.Shallow

private def seededClass : Ariadne.Class := Extracted_classes.program.classes[1]!
private def constructor : Ariadne.Function := seededClass.constructor_.getD default
private def seededLayout : DataRelation Value NativeTypes.«Seeded#state» :=
  ((DataRelation.field "value" DataRelation.int DataRelation.fieldsNil).classState "Seeded").comap
    NativeDestruct.«Seeded#state»

/-- Fresh construction matches the actual emitted constructor for every
ambient heap and bigint initial value. -/
theorem seeded_constructor_source (before : State) (initial : Int) :
    ∃ after, SourceEvaluates Extracted_classes.source before
      (.newClass "Seeded" [.literal (.bigint initial) {}] {}) (.ref before.heap.length) after ∧
      seededLayout.Holds after.heap (.ref before.heap.length) («Seeded##new» initial) [before.heap.length] := by
  let initialFields : List (String × Value) := [("value", .bigint 0)]
  have fieldsRelated : (DataRelation.field "value" DataRelation.int DataRelation.fieldsNil).Holds
      before.heap initialFields ((0 : Int), ()) [] :=
    ⟨.bigint 0, rfl, [], [], ⟨rfl, rfl⟩, ⟨True.intro, rfl⟩, by simp [Disjoint], rfl⟩
  let allocated := (before.alloc (.instance_ "Seeded" initialFields)).2
  have fresh := DataRelation.class_alloc (className := "Seeded") fieldsRelated
  let this : Param := {name := "this", ty := .class_ "Seeded"}
  let parameter : Param := {name := "initial", ty := .bigint, span := {start := 728, stop := 735}}
  have params : constructor.params = [parameter] := by rfl
  let bound := bindArguments allocated (this :: constructor.params) [.ref before.heap.length, .bigint initial]
  have lookups : bound.lookup "this" = .ok (.ref before.heap.length) ∧ bound.lookup "initial" = .ok (.bigint initial) := by
    dsimp only [bound]; rw [params]
    exact bindArguments_two allocated this parameter (.ref before.heap.length) (.bigint initial) (by decide)
  have represented := bindArguments_data fresh (this :: constructor.params) [.ref before.heap.length, .bigint initial]
  have thisEval := Evaluates.variable Extracted_classes.program bound "this" {start := 747, stop := 751}
    (.ref before.heap.length) (State.lookup_present lookups.1) lookups.1
  have initialEval := Evaluates.variable Extracted_classes.program bound "initial" {start := 760, stop := 767}
    (.bigint initial) (State.lookup_present lookups.2) lookups.2
  obtain ⟨updated, assigned, related, _⟩ := class_scalar_assign "Seeded" "value"
    (.var "this" {start := 747, stop := 751}) (.var "initial" {start := 760, stop := 767}) (.bigint initial)
    {start := 747, stop := 757} {start := 747, stop := 757}
    represented (IgnoresField.nil "value") thisEval initialEval rfl
  have body := ExecutesStatement.block
    (ExecutesBlock.next assigned rfl (ExecutesBlock.nil Extracted_classes.program updated)) {start := 745, stop := 770}
  have completed := CompletesBody.statement
    (show ExecutesStatement Extracted_classes.program bound constructor.body _ from body) (Or.inl rfl)
  have fieldsEval : EvaluatesFields Extracted_classes.program before
      (seededClass.fields.map fun f => (f.name, f.value)) [] initialFields before := by
    exact EvaluatesFields.cons (Evaluates.literal _ _ (.bigint 0) {start := 710, stop := 712})
      (EvaluatesFields.nil _ _ initialFields) (by decide)
  have evaluated := Evaluates.newClass_constructor
    (by kernel_rfl : Extracted_classes.program.classes.find? (·.name == seededClass.name) = some seededClass)
    (by kernel_rfl : seededClass.constructor_ = some constructor)
    (EvaluatesArgs.cons (Evaluates.literal _ before (.bigint initial) {}) (EvaluatesArgs.nil _ before))
    fieldsEval completed {}
  have emitted : «Seeded##new» initial = NativeTypes.«Seeded#state».mk initial := by rfl
  rw [emitted]
  exact ⟨{updated with env := before.env}, Extracted_classes.certificate.transfer_evaluation evaluated, related⟩

private def counterClass : Ariadne.Class := Extracted_classes.program.classes[0]!
private def freshCounterLayout : DataRelation Value NativeTypes.«Counter#state» :=
  ((DataRelation.field "counts" (DataRelation.map DataRelation.string DataRelation.int)
    (DataRelation.field "value" DataRelation.int DataRelation.fieldsNil)).classState "Counter").comap
    (fun native => (native.counts, (native.value, ())))

/-- The default constructor allocates its private Map before its fresh class
root, preserving the original heap and the emitted native empty state. -/
theorem counter_constructor_source (before : State) :
    ∃ after, SourceEvaluates Extracted_classes.source before (.newClass "Counter" [] {})
      (.ref (before.heap.length + 1)) after ∧
      freshCounterLayout.Holds after.heap (.ref (before.heap.length + 1)) «Counter##new»
        [before.heap.length + 1, before.heap.length] := by
  let mapped := (before.alloc (.map [])).2
  let fields : List (String × Value) := [("value", .bigint 0), ("counts", .ref before.heap.length)]
  have mapRelated := DataRelation.map_alloc DataRelation.string DataRelation.int before
  have fieldsRelated : (DataRelation.field "counts" (DataRelation.map DataRelation.string DataRelation.int)
      (DataRelation.field "value" DataRelation.int DataRelation.fieldsNil)).Holds
      mapped.heap fields (JSMap.empty, (0, ())) [before.heap.length] := by
    exact ⟨.ref before.heap.length, rfl, [before.heap.length], [], mapRelated,
      ⟨.bigint 0, rfl, [], [], ⟨rfl, rfl⟩, ⟨True.intro, rfl⟩, by simp [Disjoint], rfl⟩,
      by simp [Disjoint], rfl⟩
  have initializers : EvaluatesFields Extracted_classes.program before
      (counterClass.fields.map fun f => (f.name, f.value)) [] fields mapped := by
    exact EvaluatesFields.cons (Evaluates.literal _ _ (.bigint 0) {start := 41, stop := 43})
      (EvaluatesFields.cons (Evaluates.newMap _ before .string .bigint {start := 77, stop := 80})
        (EvaluatesFields.nil _ mapped fields) (by decide)) (by decide)
  have fresh := DataRelation.class_alloc (className := "Counter") fieldsRelated
  have evaluated := Evaluates.newClass_plain
    (by kernel_rfl : Extracted_classes.program.classes.find? (·.name == counterClass.name) = some counterClass)
    (by kernel_rfl : counterClass.constructor_ = none) (EvaluatesArgs.nil _ before) initializers {}
  have className : counterClass.name = "Counter" := rfl
  refine ⟨(mapped.alloc (.instance_ "Counter" fields)).2, Extracted_classes.certificate.transfer_evaluation ?_, ?_⟩
  · change Evaluates Extracted_classes.program before (.newClass "Counter" [] {})
      (.ref (before.heap.length + 1)) (mapped.alloc (.instance_ "Counter" fields)).2
    simpa only [className, mapped, State.alloc, List.length_append, List.length_singleton] using evaluated
  · change ((DataRelation.field "counts" (DataRelation.map DataRelation.string DataRelation.int)
      (DataRelation.field "value" DataRelation.int DataRelation.fieldsNil)).classState "Counter").Holds
      (mapped.alloc (.instance_ "Counter" fields)).2.heap (.ref (before.heap.length + 1))
      (JSMap.empty, (0, ())) [before.heap.length + 1, before.heap.length]
    simpa only [mapped, State.alloc, List.length_append, List.length_singleton] using fresh

/-- Fresh construction followed by an arbitrary add/read trace agrees with
both the emitted constructor and every emitted method result. -/
theorem seeded_fresh_trace_source (before : State) (initial : Int) (amounts : List Int) :
    ∃ initialized after,
      SourceEvaluates Extracted_classes.source before (.newClass "Seeded" [.literal (.bigint initial) {}] {})
        (.ref before.heap.length) initialized ∧
      SourceTrace Extracted_classes.source initialized (seededCalls before.heap.length amounts)
        (seededNativeTrace («Seeded##new» initial) amounts).2 after ∧
      seededLayout.Holds after.heap (.ref before.heap.length)
        (seededNativeTrace («Seeded##new» initial) amounts).1 [before.heap.length] := by
  obtain ⟨initialized, constructed, represented⟩ := seeded_constructor_source before initial
  obtain ⟨after, traced, related⟩ := seeded_trace_source initialized before.heap.length [before.heap.length]
    («Seeded##new» initial) amounts represented
  exact ⟨initialized, after, constructed, traced, related⟩

/-- Fresh private Map construction followed by an arbitrary bump/count trace. -/
theorem counter_fresh_trace_source (before : State) (keys : List JSString) :
    ∃ initialized after,
      SourceEvaluates Extracted_classes.source before (.newClass "Counter" [] {})
        (.ref (before.heap.length + 1)) initialized ∧
      SourceTrace Extracted_classes.source initialized (counterCalls (before.heap.length + 1) keys)
        (counterNativeTrace «Counter##new» keys).2 after ∧
      freshCounterLayout.Holds after.heap (.ref (before.heap.length + 1))
        (counterNativeTrace «Counter##new» keys).1 [before.heap.length + 1, before.heap.length] := by
  obtain ⟨initialized, constructed, represented⟩ := counter_constructor_source before
  obtain ⟨after, traced, related⟩ := counter_trace_source initialized (before.heap.length + 1)
    [before.heap.length + 1, before.heap.length] «Counter##new» keys represented
  exact ⟨initialized, after, constructed, traced, related⟩

end Examples.ClassAdequacy
