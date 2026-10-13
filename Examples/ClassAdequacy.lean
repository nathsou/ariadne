import Ariadne.Shallow.Adequacy.ClassMutation
import Ariadne.SourceTrace
import Examples.Shallow.classes

namespace Examples.ClassAdequacy
open Ariadne Ariadne.Shallow Ariadne.Shallow.Adequacy
open Extracted_classes.Shallow

private def seeded : Ariadne.Class := Extracted_classes.program.classes[1]!
private def addMethod : Ariadne.Function := seeded.methods[0]!
private def layout : DataRelation Value NativeTypes.«Seeded#state» :=
  ((DataRelation.field "value" DataRelation.int DataRelation.fieldsNil).classState "Seeded").comap
    NativeDestruct.«Seeded#state»

/-- The original private-field method agrees with its emitted native state
update for every related external heap and arbitrary bigint amount. -/
theorem seeded_add_source (before : State) (address : Nat) (owned : Heap.Footprint)
    (native : NativeTypes.«Seeded#state») (amount : Int)
    (input : layout.Holds before.heap (.ref address) native owned) :
    ∃ after, SourceInvokes Extracted_classes.source before (.method address "add") [.bigint amount]
      .undefined after ∧ layout.Holds after.heap (.ref address) («Seeded#add» native amount).2.1 owned := by
  have canonical : ((DataRelation.field "value" DataRelation.int DataRelation.fieldsNil).classState "Seeded").Holds
      before.heap (.ref address) (native.value, ()) owned := input
  obtain ⟨root, fields, children, same, receiver, _, _, _⟩ := class_contents canonical
  have equal : address = root := Value.ref.inj same
  subst root
  let this : Param := {name := "this", ty := .class_ "Seeded"}
  let parameter : Param := {name := "amount", ty := .bigint, span := {start := 777, stop := 783}}
  have params : addMethod.params = [parameter] := by rfl
  let state := bindArguments before (this :: addMethod.params) [.ref address, .bigint amount]
  have lookups : state.lookup "this" = .ok (.ref address) ∧ state.lookup "amount" = .ok (.bigint amount) := by
    dsimp only [state]
    rw [params]
    exact bindArguments_two before this parameter (.ref address) (.bigint amount) (by decide)
  have represented := bindArguments_data canonical (this :: addMethod.params) [.ref address, .bigint amount]
  obtain ⟨value, read, encoded⟩ := class_scalar_get represented
  have valueEq : value = .bigint native.value := encoded
  subst value
  have thisEval := Evaluates.variable Extracted_classes.program state "this" {start := 814, stop := 818}
    (.ref address) (State.lookup_present lookups.1) lookups.1
  have fieldEval := thisEval.member "value" {start := 814, stop := 824} read
  have amountEval := Evaluates.variable Extracted_classes.program state "amount" {start := 827, stop := 833}
    (.bigint amount) (State.lookup_present lookups.2) lookups.2
  have rhsEval := fieldEval.binary amountEval "+" {start := 814, stop := 833} (by decide) (by rfl)
  have result := class_scalar_assign_method_source Extracted_classes.certificate seeded addMethod before address fields
    [.bigint amount] native.value (native.value + amount) () owned "value"
    (.binary "+" (.member (.var "this" {start := 814, stop := 818}) "value" {start := 814, stop := 824})
      (.var "amount" {start := 827, stop := 833}) {start := 814, stop := 833})
    (.bigint (native.value + amount)) {start := 801, stop := 805} {start := 801, stop := 811}
    {start := 801, stop := 811} {start := 799, stop := 836}
    receiver (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) lookups.1 canonical
    (IgnoresField.nil "value") rhsEval rfl
  exact result

private def readMethod : Ariadne.Function := seeded.methods[1]!

/-- Reading the private state agrees with the actual emitted method and
retains the class representation for subsequent calls. -/
theorem seeded_read_source (before : State) (address : Nat) (owned : Heap.Footprint)
    (native : NativeTypes.«Seeded#state»)
    (input : layout.Holds before.heap (.ref address) native owned) :
    ∃ after, SourceInvokes Extracted_classes.source before (.method address "read") []
      (.bigint («Seeded#read» native)) after ∧ layout.Holds after.heap (.ref address) native owned := by
  have canonical : ((DataRelation.field "value" DataRelation.int DataRelation.fieldsNil).classState "Seeded").Holds
      before.heap (.ref address) (native.value, ()) owned := input
  obtain ⟨root, fields, children, same, receiver, _, _, _⟩ := class_contents canonical
  have equal : address = root := Value.ref.inj same
  subst root
  have params : readMethod.params = [] := by kernel_rfl
  have thisLookup : (bindArguments before ({name := "this", ty := .class_ seeded.name} :: readMethod.params)
      [.ref address]).lookup "this" = .ok (.ref address) := by
    rw [params]
    exact lookup_declare_self _ "this" (.ref address)
  obtain ⟨value, after, invoked, encoded, related⟩ := class_scalar_read_method_source
    Extracted_classes.certificate seeded readMethod before address fields [] native.value () owned "value"
    {start := 863, stop := 867} {start := 863, stop := 873} {start := 856, stop := 862} {start := 854, stop := 876}
    receiver (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) thisLookup canonical
  change value = .bigint native.value at encoded
  subst value
  exact ⟨after, invoked, related⟩

/-- The native observations use the emitted methods at every step. -/
def seededNativeTrace (native : NativeTypes.«Seeded#state») : List Int → NativeTypes.«Seeded#state» × List Value
  | [] => (native, [])
  | amount :: amounts =>
    let updated := («Seeded#add» native amount).2.1
    let (final, rest) := seededNativeTrace updated amounts
    (final, .undefined :: .bigint («Seeded#read» updated) :: rest)

def seededCalls (address : Nat) (amounts : List Int) : List (Value × List Value) :=
  amounts.flatMap fun amount => [(.method address "add", [.bigint amount]), (.method address "read", [])]

/-- Arbitrarily long add/read traces agree with the emitted native states and
observations, starting from any related external class instance. -/
theorem seeded_trace_source (before : State) (address : Nat) (owned : Heap.Footprint)
    (native : NativeTypes.«Seeded#state») (amounts : List Int)
    (input : layout.Holds before.heap (.ref address) native owned) :
    ∃ after, SourceTrace Extracted_classes.source before (seededCalls address amounts)
      (seededNativeTrace native amounts).2 after ∧
      layout.Holds after.heap (.ref address) (seededNativeTrace native amounts).1 owned := by
  induction amounts generalizing before native with
  | nil => exact ⟨before, .nil before, input⟩
  | cons amount amounts ih =>
    obtain ⟨added, addInvoked, updated⟩ := seeded_add_source before address owned native amount input
    obtain ⟨read, readInvoked, unchanged⟩ := seeded_read_source added address owned _ updated
    obtain ⟨after, rest, represented⟩ := ih read _ unchanged
    exact ⟨after, .next addInvoked (.next readInvoked rest), represented⟩

end Examples.ClassAdequacy
