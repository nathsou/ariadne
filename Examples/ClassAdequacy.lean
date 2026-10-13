import Ariadne.Shallow.Adequacy.ClassMutation
import Ariadne.SourceTrace
import Ariadne.Shallow.Adequacy.MapExpressions
import Examples.Shallow.classes

namespace Examples.ClassAdequacy
open Ariadne Ariadne.Shallow Ariadne.Shallow.Adequacy
open Extracted_classes.Shallow
open Heap

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

private def counter : Ariadne.Class := Extracted_classes.program.classes[0]!
private def bumpMethod : Ariadne.Function := counter.methods[2]!
private def countsLayout := DataRelation.map DataRelation.string DataRelation.int
private def counterLayout : DataRelation Value NativeTypes.«Counter#state» :=
  ((DataRelation.field "counts" countsLayout (DataRelation.field "value" DataRelation.int DataRelation.fieldsNil)).classState "Counter").comap
    (fun native => (native.counts, (native.value, ())))

theorem counter_bump_source (before : State) (address : Nat) (owned : Footprint)
    (native : NativeTypes.«Counter#state») (key : JSString)
    (input : counterLayout.Holds before.heap (.ref address) native owned) :
    ∃ after, SourceInvokes Extracted_classes.source before (.method address "bump") [.string key]
      (.bigint («Counter#bump» native key).1) after ∧
      counterLayout.Holds after.heap (.ref address) («Counter#bump» native key).2.1 owned := by
  have canonical : ((DataRelation.field "counts" countsLayout
      (DataRelation.field "value" DataRelation.int DataRelation.fieldsNil)).classState "Counter").Holds
      before.heap (.ref address) (native.counts, (native.value, ())) owned := input
  obtain ⟨root, fields, children, same, receiver, _, _, _⟩ := class_contents canonical
  have equal : address = root := Value.ref.inj same
  subst root
  let this : Param := {name := "this", ty := .class_ "Counter"}
  let parameter : Param := {name := "key", ty := .string, span := {start := 213, stop := 216}}
  have params : bumpMethod.params = [parameter] := by rfl
  let state := bindArguments before (this :: bumpMethod.params) [.ref address, .string key]
  have lookups : state.lookup "this" = .ok (.ref address) ∧ state.lookup "key" = .ok (.string key) := by
    dsimp only [state]; rw [params]
    exact bindArguments_two before this parameter (.ref address) (.string key) (by decide)
  have framed := bindArguments_data canonical (this :: bumpMethod.params) [.ref address, .string key]
  obtain ⟨value, selected, countsRead, subset, mapRelated, rebuild⟩ := class_field_focus framed
  obtain ⟨mapAddress, entries, _, mapRef, mapLookup, _, _, _⟩ := map_contents mapRelated
  subst value
  have selectedEq := scalar_map_footprint mapRelated
  let next := (native.counts.get key).getD 0 + 1
  have thisEval := Evaluates.variable Extracted_classes.program state "this" {start := 254, stop := 258}
    (.ref address) (State.lookup_present lookups.1) lookups.1
  have keyEval := Evaluates.variable Extracted_classes.program state "key" {start := 270, stop := 273}
    (.string key) (State.lookup_present lookups.2) lookups.2
  have initial := map_get_int_default
    (.member (.var "this" {start := 254, stop := 258}) "counts" {start := 254, stop := 265})
    (.var "key" {start := 270, stop := 273}) key (.string key) 0
    {start := 254, stop := 269} {start := 254, stop := 274} {start := 278, stop := 280} {start := 254, stop := 280}
    mapRelated (thisEval.member "counts" {start := 254, stop := 265} countsRead) keyEval
    (fun same => by cases same; rfl)
  have computed := initial.binary (Evaluates.literal Extracted_classes.program state (.bigint 1) {start := 284, stop := 286})
    "+" {start := 254, stop := 286} (by decide) (show binary "+" (.bigint ((native.counts.get key).getD 0)) (.bigint 1) = .ok (.bigint next) from rfl)
  let declared := state.declare "next" (.bigint next)
  have thisLookup := lookup_declare_other (name := "next") (value := .bigint next) (by decide : "next" ≠ "this") lookups.1
  have keyLookup := lookup_declare_other (name := "next") (value := .bigint next) (by decide : "next" ≠ "key") lookups.2
  have nextLookup := lookup_declare_self state "next" (.bigint next)
  have mapAfterLet : countsLayout.Holds declared.heap (.ref mapAddress) native.counts selected :=
    countsLayout.frame mapRelated (state.alloc_frame (.cell (.bigint next)) selected (countsLayout.allocated mapRelated))
  obtain ⟨afterRoot, afterEntries, _, afterSame, mapAfterLookup, _, _, _⟩ := map_contents mapAfterLet
  have rootEqual : mapAddress = afterRoot := Value.ref.inj afterSame
  subst afterRoot
  have classAllocated : address < state.heap.length := by
    obtain ⟨_, _, _, same, found, _, _, _⟩ := class_contents framed
    cases same
    exact (List.getElem?_eq_some_iff.mp found).choose
  have countsReadAfter : readMember declared (.ref address) "counts" = .ok (.ref mapAddress) := by
    simpa [readMember, declared, State.declare, State.alloc, List.getElem?_append_left classAllocated] using countsRead
  have localThis := Evaluates.variable Extracted_classes.program declared "this" {start := 292, stop := 296}
    (.ref address) (State.lookup_present thisLookup) thisLookup
  have container := localThis.member "counts" {start := 292, stop := 303} countsReadAfter
  have setMethod : Evaluates Extracted_classes.program declared
      (.member (.member (.var "this" {start := 292, stop := 296}) "counts" {start := 292, stop := 303}) "set" {start := 292, stop := 307})
      (.method mapAddress "set") declared :=
    container.member "set" {start := 292, stop := 307} (by simp [readMember, mapAfterLookup, pure, Except.pure])
  have keyArg := Evaluates.variable Extracted_classes.program declared "key" {start := 308, stop := 311}
    (.string key) (State.lookup_present keyLookup) keyLookup
  have nextArg := Evaluates.variable Extracted_classes.program declared "next" {start := 313, stop := 317}
    (.bigint next) (State.lookup_present nextLookup) nextLookup
  obtain ⟨after, inserted, updated, writes⟩ := map_set_scalar (program := Extracted_classes.program) mapAfterLet key
    (.string key) (.bigint next) next (fun same => by cases same; rfl) rfl rfl
  have setEval := Evaluates.call setMethod (EvaluatesArgs.cons keyArg (EvaluatesArgs.cons nextArg (EvaluatesArgs.nil _ _))) inserted {start := 292, stop := 318}
  have sameEnv := inserted.map_set_env mapAfterLookup
  have mapAllocated : mapAddress < state.heap.length := (List.getElem?_eq_some_iff.mp mapLookup).choose
  have stored : after.heap[state.heap.length]? = some (.cell (.bigint next)) := by
    have unchanged := writes.2 state.heap.length (by simp [declared, State.declare, State.alloc])
      (by simp only [List.mem_singleton]; omega)
    exact unchanged.symm.trans (state.alloc_lookup (.cell (.bigint next)))
  have finalLookup : after.lookup "next" = .ok (.bigint next) := by
    simp [State.lookup, sameEnv, declared, State.declare, State.alloc, stored, pure, Except.pure]
  have returned := Evaluates.variable Extracted_classes.program after "next" {start := 331, stop := 335}
    (.bigint next) (State.lookup_present finalLookup) finalLookup
  have body := ExecutesStatement.block
    (ExecutesBlock.next (ExecutesStatement.let_ computed false "next" none {start := 240, stop := 245}) rfl
      (ExecutesBlock.next (ExecutesStatement.expression setEval {start := 292, stop := 318}) rfl
        (ExecutesBlock.stop (ExecutesStatement.return_ returned {start := 324, stop := 330}) [] (by intro h; cases h))))
    {start := 234, stop := 340}
  have invoked := invoke_method_completion receiver (by kernel_rfl : Extracted_classes.program.classes.find? (·.name == counter.name) = some counter)
    (by kernel_rfl : counter.methods.find? (·.name == bumpMethod.name) = some bumpMethod)
    (show ExecutesStatement Extracted_classes.program state bumpMethod.body _ from body) (Or.inr rfl)
  have modified : Modifies selected state.heap after.heap := by
    rw [selectedEq]
    exact (modifies_append state.heap [.cell (.bigint next)] [mapAddress]).trans writes
  have rebuilt := rebuild after.heap (native.counts.set key next) updated modified
  have emitted : «Counter#bump» native key =
      (next, (NativeTypes.«Counter#state».mk native.value (native.counts.set key next), ())) := by
    cases found : native.counts.get key <;>
      simp [«Counter#bump», NativeConstruct.«Counter#state», NativeDestruct.«Counter#state», next, found]
  rw [emitted]
  exact ⟨{after with env := before.env}, Extracted_classes.certificate.transfer_invocation invoked, rebuilt⟩

private def countMethod : Ariadne.Function := counter.methods[3]!

/-- Private Map reads agree with the emitted method for arbitrary UTF-16 keys,
including missing keys, and retain the complete class representation. -/
theorem counter_count_source (before : State) (address : Nat) (owned : Footprint)
    (native : NativeTypes.«Counter#state») (key : JSString)
    (input : counterLayout.Holds before.heap (.ref address) native owned) :
    ∃ after, SourceInvokes Extracted_classes.source before (.method address "count") [.string key]
      (.bigint («Counter#count» native key)) after ∧
      counterLayout.Holds after.heap (.ref address) native owned := by
  have canonical : ((DataRelation.field "counts" countsLayout
      (DataRelation.field "value" DataRelation.int DataRelation.fieldsNil)).classState "Counter").Holds
      before.heap (.ref address) (native.counts, (native.value, ())) owned := input
  obtain ⟨root, fields, children, same, receiver, _, _, _⟩ := class_contents canonical
  have equal : address = root := Value.ref.inj same
  subst root
  let this : Param := {name := "this", ty := .class_ "Counter"}
  let parameter : Param := {name := "key", ty := .string, span := {start := 349, stop := 352}}
  have params : countMethod.params = [parameter] := by rfl
  let state := bindArguments before (this :: countMethod.params) [.ref address, .string key]
  have lookups : state.lookup "this" = .ok (.ref address) ∧ state.lookup "key" = .ok (.string key) := by
    dsimp only [state]; rw [params]
    exact bindArguments_two before this parameter (.ref address) (.string key) (by decide)
  have framed := bindArguments_data canonical (this :: countMethod.params) [.ref address, .string key]
  obtain ⟨value, selected, countsRead, _, mapRelated, _⟩ := class_field_focus framed
  obtain ⟨mapAddress, _, _, mapRef, _, _, _, _⟩ := map_contents mapRelated
  subst value
  have thisEval := Evaluates.variable Extracted_classes.program state "this" {start := 379, stop := 383}
    (.ref address) (State.lookup_present lookups.1) lookups.1
  have keyEval := Evaluates.variable Extracted_classes.program state "key" {start := 395, stop := 398}
    (.string key) (State.lookup_present lookups.2) lookups.2
  have evaluated := map_get_int_default
    (.member (.var "this" {start := 379, stop := 383}) "counts" {start := 379, stop := 390})
    (.var "key" {start := 395, stop := 398}) key (.string key) 0
    {start := 379, stop := 394} {start := 379, stop := 399} {start := 403, stop := 405} {start := 379, stop := 405}
    mapRelated (thisEval.member "counts" {start := 379, stop := 390} countsRead) keyEval
    (fun same => by cases same; rfl)
  have body := ExecutesStatement.block
    (ExecutesBlock.stop (ExecutesStatement.return_ evaluated {start := 372, stop := 378}) [] (by intro h; cases h))
    {start := 370, stop := 408}
  have invoked := invoke_method_completion receiver (by kernel_rfl : Extracted_classes.program.classes.find? (·.name == counter.name) = some counter)
    (by kernel_rfl : counter.methods.find? (·.name == countMethod.name) = some countMethod)
    (show ExecutesStatement Extracted_classes.program state countMethod.body _ from body) (Or.inr rfl)
  have emitted : «Counter#count» native key = (native.counts.get key).getD 0 := by
    cases found : native.counts.get key <;> simp [«Counter#count», NativeDestruct.«Counter#state», found]
  rw [emitted]
  exact ⟨{state with env := before.env}, Extracted_classes.certificate.transfer_invocation invoked, framed⟩

def counterNativeTrace (native : NativeTypes.«Counter#state») : List JSString → NativeTypes.«Counter#state» × List Value
  | [] => (native, [])
  | key :: keys =>
    let (value, updated, _) := «Counter#bump» native key
    let (final, rest) := counterNativeTrace updated keys
    (final, .bigint value :: .bigint («Counter#count» updated key) :: rest)

def counterCalls (address : Nat) (keys : List JSString) : List (Value × List Value) :=
  keys.flatMap fun key => [(.method address "bump", [.string key]), (.method address "count", [.string key])]

/-- Arbitrary-length private Map call traces preserve the actual class state
and match every emitted native observation. -/
theorem counter_trace_source (before : State) (address : Nat) (owned : Footprint)
    (native : NativeTypes.«Counter#state») (keys : List JSString)
    (input : counterLayout.Holds before.heap (.ref address) native owned) :
    ∃ after, SourceTrace Extracted_classes.source before (counterCalls address keys)
      (counterNativeTrace native keys).2 after ∧
      counterLayout.Holds after.heap (.ref address) (counterNativeTrace native keys).1 owned := by
  induction keys generalizing before native with
  | nil => exact ⟨before, .nil before, input⟩
  | cons key keys ih =>
    obtain ⟨bumped, bumpInvoked, updated⟩ := counter_bump_source before address owned native key input
    obtain ⟨counted, countInvoked, unchanged⟩ := counter_count_source bumped address owned _ key updated
    obtain ⟨after, rest, represented⟩ := ih counted _ unchanged
    exact ⟨after, .next bumpInvoked (.next countInvoked rest), represented⟩

/-- The certified runtime method guard composes with the proved source behavior. -/
theorem seeded_add_wrapper_source (before : State) (address : Nat) (owned : Footprint)
    (native : NativeTypes.«Seeded#state») (amount : Int)
    (input : layout.Holds before.heap (.ref address) native owned) :
    ∃ after, Ownership.WrappedSourceMethodInvokes Extracted_classes.source Extracted_classes.Wrapper.source
      "Seeded" "add" before address [.bigint amount] .undefined after ∧
      layout.Holds after.heap (.ref address) («Seeded#add» native amount).2.1 owned := by
  obtain ⟨root, fields, children, same, lookup, _, _, _⟩ := class_contents input
  have equal : address = root := Value.ref.inj same
  subst root
  obtain ⟨after, invoked, related⟩ := seeded_add_source before address owned native amount input
  exact ⟨after, MethodEntries.«Seeded».«add».certificate.transfer ⟨fields, lookup⟩ invoked rfl, related⟩

/-- The certified runtime method guard composes with the proved source behavior. -/
theorem seeded_read_wrapper_source (before : State) (address : Nat) (owned : Footprint)
    (native : NativeTypes.«Seeded#state»)
    (input : layout.Holds before.heap (.ref address) native owned) :
    ∃ after, Ownership.WrappedSourceMethodInvokes Extracted_classes.source Extracted_classes.Wrapper.source
      "Seeded" "read" before address [] (.bigint («Seeded#read» native)) after ∧
      layout.Holds after.heap (.ref address) native owned := by
  obtain ⟨root, fields, children, same, lookup, _, _, _⟩ := class_contents input
  have equal : address = root := Value.ref.inj same
  subst root
  obtain ⟨after, invoked, related⟩ := seeded_read_source before address owned native input
  exact ⟨after, MethodEntries.«Seeded».«read».certificate.transfer ⟨fields, lookup⟩ invoked rfl, related⟩

/-- The certified runtime method guard composes with the proved source behavior. -/
theorem counter_bump_wrapper_source (before : State) (address : Nat) (owned : Footprint)
    (native : NativeTypes.«Counter#state») (key : JSString)
    (input : counterLayout.Holds before.heap (.ref address) native owned) :
    ∃ after, Ownership.WrappedSourceMethodInvokes Extracted_classes.source Extracted_classes.Wrapper.source
      "Counter" "bump" before address [.string key] (.bigint («Counter#bump» native key).1) after ∧
      counterLayout.Holds after.heap (.ref address) («Counter#bump» native key).2.1 owned := by
  obtain ⟨root, fields, children, same, lookup, _, _, _⟩ := class_contents input
  have equal : address = root := Value.ref.inj same
  subst root
  obtain ⟨after, invoked, related⟩ := counter_bump_source before address owned native key input
  exact ⟨after, MethodEntries.«Counter».«bump».certificate.transfer ⟨fields, lookup⟩ invoked rfl, related⟩

/-- The certified runtime method guard composes with the proved source behavior. -/
theorem counter_count_wrapper_source (before : State) (address : Nat) (owned : Footprint)
    (native : NativeTypes.«Counter#state») (key : JSString)
    (input : counterLayout.Holds before.heap (.ref address) native owned) :
    ∃ after, Ownership.WrappedSourceMethodInvokes Extracted_classes.source Extracted_classes.Wrapper.source
      "Counter" "count" before address [.string key] (.bigint («Counter#count» native key)) after ∧
      counterLayout.Holds after.heap (.ref address) native owned := by
  obtain ⟨root, fields, children, same, lookup, _, _, _⟩ := class_contents input
  have equal : address = root := Value.ref.inj same
  subst root
  obtain ⟨after, invoked, related⟩ := counter_count_source before address owned native key input
  exact ⟨after, MethodEntries.«Counter».«count».certificate.transfer ⟨fields, lookup⟩ invoked rfl, related⟩

end Examples.ClassAdequacy
