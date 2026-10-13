import Ariadne.Shallow.Elaborate
import Ariadne.Shallow.Adequacy.ProjectionSource

namespace Ariadne.Shallow.ProjectionEmit
open Core

private def ident (name : String) := "«" ++ name ++ "»"
private def compact {α : Type} [Repr α] (value : α) := (repr value).pretty 10000000

/-- This first stateful source witness covers the exact parsed projection and
the actual emitted native definition. Other mutation shapes are left pending. -/
private def mapSourceTheorem (namespace_ : String) (f : Ariadne.Function) (core : Core.Function)
    (params : String) (names : List String) (publicAlias : Bool) : Option String := do
  if !f.exported then none else pure ()
  let [mapParam, keyParam, valueParam] := f.params | none
  let [map, key, value] := names | none
  if core.params != [.map .string (.list .int), .string, .int] ||
      core.result != .pair .unit (.pair (.map .string (.list .int)) .unit) then none else pure ()
  let .block [.expr
      (.call (.member (.unary "#nonNull"
        (.call (.member (.var mapName mapSpan) "get" getMember) [.var keyName keySpan] getCall)
        assertion) "push" pushMember) [.var valueName valueSpan] pushCall) statementSpan] blockSpan := f.body | none
  if mapName != mapParam.name || keyName != keyParam.name || valueName != valueParam.name then none else pure ()
  let function := "EntryGuards." ++ ident f.name ++ ".function"
  let check := "SourceProjectionChecks." ++ ident f.name
  let coreName := "CoreArtifacts." ++ ident f.name
  let call := ident f.name ++ String.join (names.map (" " ++ ·))
  let theoremName := if publicAlias then ident (f.name ++ "_source") else check ++ ".source"
  let layout := "(DataRelation.map DataRelation.string DataRelation.int.array)"
  let args := s!"[.ref _sourceAddress, .string {key}, .bigint {value}]"
  let spans := String.join ([mapSpan, keySpan, valueSpan, getMember, getCall,
    assertion, pushMember, pushCall, statementSpan, blockSpan].map (fun span => " (" ++ compact span ++ ")"))
  return s!"theorem {check}.parameters : {function}.params = {compact f.params} := by kernel_rfl\n\n" ++
    s!"theorem {theoremName}{params} (_sourceHeap : Heap) (_sourceAddress : Nat) (_sourceFootprint : Heap.Footprint)\n" ++
    s!"    (_sourceInput : {layout}.Holds _sourceHeap (.ref _sourceAddress) {map} _sourceFootprint)\n" ++
    s!"    (_sourceSafe : {ident f.name}.safe{String.join (names.map (" " ++ ·))}) :\n" ++
    s!"    Adequacy.SourceMutatesFrom _root_.{namespace_}.source {compact f.name} _sourceHeap {args}\n" ++
    s!"      {layout} (.ref _sourceAddress) ({call}).2.1 := by\n" ++
    "  have accepted := _sourceSafe.2\n" ++
    s!"  have selected : ∃ old, JSMap.get {map} {key} = some old ∧ (old ++ [{value}]).length < 2 ^ 32 := by\n" ++
    s!"    cases found : JSMap.get {map} {key} with\n" ++
    "    | none =>\n" ++
    s!"      simp [{coreName}, Safety.term, Safety.getVariable, Safety.binary,\n" ++
    "        Safety.binarySafe, Safety.liftEnvironment, found] at accepted\n" ++
    "    | some old =>\n      refine ⟨old, rfl, ?_⟩\n" ++
    s!"      simp [{coreName}, Safety.term, Safety.getVariable, Safety.binary,\n" ++
    "        Safety.binarySafe, Safety.mapSet, Safety.liftEnvironment, found] at accepted\n" ++
    "      simpa using accepted\n" ++
    "  obtain ⟨old, found, capacity⟩ := selected\n" ++
    s!"  have updated : ({call}).2.1 = JSMap.set {map} {key} (old ++ [{value}]) := by\n" ++
    s!"    simp [{ident f.name}, found]\n  rw [updated]\n" ++
    s!"  have lookups : (Adequacy.bindArguments \u007bheap := _sourceHeap\u007d {function}.params {args}).lookup {compact mapName} = .ok (.ref _sourceAddress) ∧\n" ++
    s!"      (Adequacy.bindArguments \u007bheap := _sourceHeap\u007d {function}.params {args}).lookup {compact keyName} = .ok (.string {key}) ∧\n" ++
    s!"      (Adequacy.bindArguments \u007bheap := _sourceHeap\u007d {function}.params {args}).lookup {compact valueName} = .ok (.bigint {value}) := by\n" ++
    s!"    rw [{check}.parameters]\n" ++
    s!"    exact Adequacy.bindArguments_three _ ({compact mapParam}) ({compact keyParam}) ({compact valueParam})\n" ++
    s!"      (.ref _sourceAddress) (.string {key}) (.bigint {value}) (by decide) (by decide) (by decide)\n" ++
    s!"  exact Adequacy.map_push_source _root_.{namespace_}.certificate {function}\n" ++
    s!"    _sourceHeap {args} _sourceAddress {map} _sourceFootprint {key} (.string {key}) (.bigint {value}) old {value}\n" ++
    s!"    {compact mapName} {compact keyName} {compact valueName}{spans}\n" ++
    "    (by kernel_rfl) (by kernel_rfl) lookups.1 lookups.2.1 lookups.2.2 _sourceInput found\n" ++
    "    (by intro source native same; cases same; rfl) rfl capacity\n\n" ++
    s!"theorem {check}.wrapperSource{params} (_sourceHeap : Heap) (_sourceAddress : Nat) (_sourceFootprint : Heap.Footprint)\n" ++
    s!"    (_sourceInput : {layout}.Holds _sourceHeap (.ref _sourceAddress) {map} _sourceFootprint)\n" ++
    s!"    (_sourceSafe : {ident f.name}.safe{String.join (names.map (" " ++ ·))})\n" ++
    s!"    (_entrySafe : {ident f.name}.entrySafe _sourceHeap {args} = true) :\n" ++
    s!"    Adequacy.WrappedSourceMutatesFrom _root_.{namespace_}.source _root_.{namespace_}.Wrapper.source\n" ++
    s!"      {compact f.name} _sourceHeap {args} {layout} (.ref _sourceAddress) ({call}).2.1 := by\n" ++
    s!"  exact Adequacy.transfer_mutation EntryGuards.{ident f.name}.certificate\n" ++
    s!"    ({theoremName}{String.join (names.map (" " ++ ·))} _sourceHeap _sourceAddress _sourceFootprint _sourceInput _sourceSafe) _entrySafe\n\n"


/-- Stateful witness for the emitted array projection, including numeric index coercion. -/
private def arraySourceTheorem (namespace_ : String) (f : Ariadne.Function) (core : Core.Function)
    (params : String) (names : List String) (publicAlias : Bool) : Option String := do
  if !f.exported then none else pure ()
  let [mapParam, keyParam, valueParam] := f.params | none
  let [map, key, value] := names | none
  if core.params != [.list (.list .int), .number, .int] ||
      core.result != .pair .unit (.pair (.list (.list .int)) .unit) then none else pure ()
  let .block [.expr
      (.call (.member (.index (.var mapName mapSpan) (.var keyName keySpan) indexSpan)
        "push" pushMember) [.var valueName valueSpan] pushCall) statementSpan] blockSpan := f.body | none
  if mapName != mapParam.name || keyName != keyParam.name || valueName != valueParam.name then none else pure ()
  let function := "EntryGuards." ++ ident f.name ++ ".function"
  let check := "SourceProjectionChecks." ++ ident f.name
  let coreName := "CoreArtifacts." ++ ident f.name
  let call := ident f.name ++ String.join (names.map (" " ++ ·))
  let theoremName := if publicAlias then ident (f.name ++ "_source") else check ++ ".source"
  let layout := "DataRelation.int.array.array"
  let args := s!"[.ref _sourceAddress, .number {key}, .bigint {value}]"
  let spans := String.join ([mapSpan, keySpan, valueSpan, indexSpan, pushMember, pushCall, statementSpan, blockSpan].map (fun span => " (" ++ compact span ++ ")"))
  return s!"theorem {check}.parameters : {function}.params = {compact f.params} := by kernel_rfl\n\n" ++
    s!"theorem {theoremName}{params} (_sourceHeap : Heap) (_sourceAddress : Nat) (_sourceFootprint : Heap.Footprint)\n" ++
    s!"    (_sourceInput : {layout}.Holds _sourceHeap (.ref _sourceAddress) {map} _sourceFootprint)\n" ++
    s!"    (_sourceSafe : {ident f.name}.safe{String.join (names.map (" " ++ ·))}) :\n" ++
    s!"    Adequacy.SourceMutatesFrom _root_.{namespace_}.source {compact f.name} _sourceHeap {args}\n" ++
    s!"      {layout} (.ref _sourceAddress) ({call}).2.1 := by\n" ++
    "  have accepted := _sourceSafe.2\n" ++
    s!"  have selected : ∃ old, JSArray.get {map} {key} = some old ∧ (old ++ [{value}]).length < 2 ^ 32 := by\n" ++
    s!"    cases found : JSArray.get {map} {key} with\n" ++
    "    | none =>\n" ++
    s!"      simp [{coreName}, Safety.term, Safety.getVariable, Safety.binary,\n" ++
    "        Safety.binarySafe, Safety.liftEnvironment, found] at accepted\n" ++
    "    | some old =>\n      refine ⟨old, rfl, ?_⟩\n" ++
    s!"      simp [{coreName}, Safety.term, Safety.getVariable, Safety.binary,\n" ++
    "        Safety.binarySafe, Safety.liftEnvironment, Safety.call2, found,\n" ++
    "        List.all_eq_true, List.mem_mapIdx] at accepted\n" ++
    s!"      cases converted : indexOf (.number {key}) with\n" ++
    "      | none => simp [JSArray.get, converted] at found\n" ++
    "      | some selected =>\n" ++
    s!"        have lookup : {map}[selected]? = some old := by simpa [JSArray.get, converted] using found\n" ++
    "        have inside := (List.getElem?_eq_some_iff.mp lookup).choose\n" ++
    "        have same := JSArray.index_number_eq converted\n" ++
    s!"        have bound := accepted (old ++ [{value}]) selected inside (by simp [same])\n" ++
    "        simpa [same] using bound\n" ++
    "  obtain ⟨old, found, capacity⟩ := selected\n" ++
    s!"  have updated : ({call}).2.1 = JSArray.map (fun item position => if position == {key} then old ++ [{value}] else item) {map} := by\n" ++
    s!"    simp [{ident f.name}, found]\n  rw [updated]\n" ++
    s!"  have lookups : (Adequacy.bindArguments \u007bheap := _sourceHeap\u007d {function}.params {args}).lookup {compact mapName} = .ok (.ref _sourceAddress) ∧\n" ++
    s!"      (Adequacy.bindArguments \u007bheap := _sourceHeap\u007d {function}.params {args}).lookup {compact keyName} = .ok (.number {key}) ∧\n" ++
    s!"      (Adequacy.bindArguments \u007bheap := _sourceHeap\u007d {function}.params {args}).lookup {compact valueName} = .ok (.bigint {value}) := by\n" ++
    s!"    rw [{check}.parameters]\n" ++
    s!"    exact Adequacy.bindArguments_three _ ({compact mapParam}) ({compact keyParam}) ({compact valueParam})\n" ++
    s!"      (.ref _sourceAddress) (.number {key}) (.bigint {value}) (by decide) (by decide) (by decide)\n" ++
    s!"  exact Adequacy.array_push_source _root_.{namespace_}.certificate {function}\n" ++
    s!"    _sourceHeap {args} _sourceAddress {map} _sourceFootprint {key} (.bigint {value}) old {value}\n" ++
    s!"    {compact mapName} {compact keyName} {compact valueName}{spans}\n" ++
    "    (by kernel_rfl) (by kernel_rfl) lookups.1 lookups.2.1 lookups.2.2 _sourceInput found\n" ++
    "    rfl capacity\n\n" ++
    s!"theorem {check}.wrapperSource{params} (_sourceHeap : Heap) (_sourceAddress : Nat) (_sourceFootprint : Heap.Footprint)\n" ++
    s!"    (_sourceInput : {layout}.Holds _sourceHeap (.ref _sourceAddress) {map} _sourceFootprint)\n" ++
    s!"    (_sourceSafe : {ident f.name}.safe{String.join (names.map (" " ++ ·))})\n" ++
    s!"    (_entrySafe : {ident f.name}.entrySafe _sourceHeap {args} = true) :\n" ++
    s!"    Adequacy.WrappedSourceMutatesFrom _root_.{namespace_}.source _root_.{namespace_}.Wrapper.source\n" ++
    s!"      {compact f.name} _sourceHeap {args} {layout} (.ref _sourceAddress) ({call}).2.1 := by\n" ++
    s!"  exact Adequacy.transfer_mutation EntryGuards.{ident f.name}.certificate\n" ++
    s!"    ({theoremName}{String.join (names.map (" " ++ ·))} _sourceHeap _sourceAddress _sourceFootprint _sourceInput _sourceSafe) _entrySafe\n\n"


/-- Field increments and parameter additions over a one-field named numeric record reuse the generic
original-statement transfer and the actual emitted native constructor. -/
private def fieldSourceTheorem (namespace_ : String) (f : Ariadne.Function) (core : Core.Function)
    (params : String) (names : List String) (publicAlias : Bool) : Option String := do
  if !f.exported then none else pure ()
  let (rowParam, keyParam, extraParam) ← match f.params with
    | [row, key] => some (row, key, none)
    | [row, key, value] => some (row, key, some value)
    | _ => none
  let (rows, key, extraName) ← match names with
    | [rows, key] => some (rows, key, none)
    | [rows, key, value] => some (rows, key, some value)
    | _ => none
  let declaration ← match core.params with
    | [.list (.named declaration), .number] => some declaration
    | [.list (.named declaration), .number, .number] => some declaration
    | _ => none
  if declaration.shape != .pair .number .unit || declaration.name.startsWith "#" ||
      core.result != .pair .unit (.pair (.list (.named declaration)) .unit) then none else pure ()
  let .block [.update (.member (.index (.var rowsName rowsSpan) (.var keyName keySpan) indexSpan)
      field fieldSpan) "+" operand statementSpan] blockSpan := f.body | none
  if rowsName != rowParam.name || keyName != keyParam.name then none else pure ()
  let (delta, operandProof) ← match operand, extraParam, extraName with
    | .literal (.number coefficient exponent) _, none, none =>
      some (s!"Float.Model.ofScientific {coefficient} ({exponent})",
        "(by exact Evaluates.literal _ _ _ _)")
    | .var valueName valueSpan, some valueParam, some value =>
      if valueName != valueParam.name then none else
        some (value, s!"(Evaluates.variable _ _ ({compact valueName}) ({compact valueSpan}) (.number {value}) (State.lookup_present lookups.2.2) lookups.2.2)")
    | _, _, _ => none
  let function := "EntryGuards." ++ ident f.name ++ ".function"
  let check := "SourceProjectionChecks." ++ ident f.name
  let native := "NativeTypes." ++ ident declaration.name
  let construct := "NativeConstruct." ++ ident declaration.name
  let destruct := "NativeDestruct." ++ ident declaration.name
  let representation := "NativeRepresentations." ++ ident declaration.name
  let coreName := "CoreArtifacts." ++ ident f.name
  let call := ident f.name ++ String.join (names.map (" " ++ ·))
  let theoremName := if publicAlias then ident (f.name ++ "_source") else check ++ ".source"
  let decode := s!"(fun row : {native} => (row.{ident field}, ()))"
  let layout := s!"((DataRelation.field {compact field} DataRelation.number DataRelation.fieldsNil).record.comap {decode}).array"
  let extraArgument := extraName.map (fun name => s!", .number {name}") |>.getD ""
  let args := s!"[.ref _sourceAddress, .number {key}{extraArgument}]"
  let extraLookup := match extraParam, extraName with
    | some valueParam, some value =>
      s!" ∧\n      (Adequacy.bindArguments \u007bheap := _sourceHeap\u007d {function}.params {args}).lookup {compact valueParam.name} = .ok (.number {value})"
    | _, _ => ""
  let lookupProof := match extraParam, extraName with
    | some valueParam, some value =>
      s!"Adequacy.bindArguments_three _ ({compact rowParam}) ({compact keyParam}) ({compact valueParam}) (.ref _sourceAddress) (.number {key}) (.number {value}) (by decide) (by decide) (by decide)"
    | _, _ =>
      s!"Adequacy.bindArguments_two _ ({compact rowParam}) ({compact keyParam}) (.ref _sourceAddress) (.number {key}) (by decide)"
  let keyLookup := if extraParam.isSome then "lookups.2.1" else "lookups.2"
  let spans := String.join ([rowsSpan, keySpan, indexSpan, fieldSpan, statementSpan, blockSpan].map
    (fun span => " (" ++ compact span ++ ")"))
  return s!"theorem {check}.parameters : {function}.params = {compact f.params} := by kernel_rfl\n\n" ++
    s!"theorem {theoremName}{params} (_sourceHeap : Heap) (_sourceAddress : Nat) (_sourceFootprint : Heap.Footprint)\n" ++
    s!"    (_sourceInput : {layout}.Holds _sourceHeap (.ref _sourceAddress) {rows} _sourceFootprint)\n" ++
    s!"    (_sourceSafe : {ident f.name}.safe{String.join (names.map (" " ++ ·))}) :\n" ++
    s!"    Adequacy.SourceMutatesFrom _root_.{namespace_}.source {compact f.name} _sourceHeap {args}\n" ++
    s!"      {layout} (.ref _sourceAddress) ({call}).2.1 := by\n" ++
    "  have accepted := _sourceSafe.2\n" ++
    s!"  have selected : ∃ old, JSArray.get {rows} {key} = some old := by\n" ++
    s!"    cases found : JSArray.get {rows} {key} with\n" ++
    "    | none =>\n" ++
    s!"      dsimp [{coreName}, Safety.term, Safety.getVariable, Safety.binary,\n" ++
    s!"        Safety.liftEnvironment, Safety.Model, Core.Ty.denote, Interpretation.value,\n" ++
    s!"        {representation}, Named.Interp.insert, Named.Representation.transport] at accepted\n" ++
    "      set_option backward.isDefEq.respectTransparency false in\n" ++
    "        simp only [cast_eq] at accepted\n" ++
    "      simp [found, Safety.binarySafe] at accepted\n" ++
    "    | some old => exact ⟨old, rfl⟩\n" ++
    "  obtain ⟨old, found⟩ := selected\n" ++
    s!"  let delta := {delta}\n" ++
    s!"  let replacement : {native} := ⟨old.{ident field} + delta⟩\n" ++
    s!"  have updated : ({call}).2.1 = JSArray.map (fun item position => if position == {key} then replacement else item) {rows} := by\n" ++
    s!"    simp [{ident f.name}, found, {construct}, {destruct}, replacement, delta]\n" ++
    "  rw [updated]\n" ++
    s!"  have lookups : (Adequacy.bindArguments \u007bheap := _sourceHeap\u007d {function}.params {args}).lookup {compact rowsName} = .ok (.ref _sourceAddress) ∧\n" ++
    s!"      (Adequacy.bindArguments \u007bheap := _sourceHeap\u007d {function}.params {args}).lookup {compact keyName} = .ok (.number {key}){extraLookup} := by\n" ++
    s!"    rw [{check}.parameters]\n" ++
    s!"    exact {lookupProof}\n" ++
    s!"  exact Adequacy.array_record_source _root_.{namespace_}.certificate {function}\n" ++
    s!"    _sourceHeap {args} _sourceAddress {rows} _sourceFootprint {key} old replacement old.{ident field} (old.{ident field} + delta) ()\n" ++
    s!"    {decode} {compact field} \"+\" {compact rowsName} {compact keyName}\n" ++
    s!"    ({compact operand}) (.number delta) (.number (old.{ident field} + delta)){spans}\n" ++
    s!"    (by kernel_rfl) (by kernel_rfl) lookups.1 {keyLookup} _sourceInput found rfl rfl\n" ++
    s!"    (Adequacy.IgnoresField.nil {compact field}) {operandProof}\n" ++
    "    (by intro before same; cases same; rfl) rfl\n\n" ++
    s!"theorem {check}.wrapperSource{params} (_sourceHeap : Heap) (_sourceAddress : Nat) (_sourceFootprint : Heap.Footprint)\n" ++
    s!"    (_sourceInput : {layout}.Holds _sourceHeap (.ref _sourceAddress) {rows} _sourceFootprint)\n" ++
    s!"    (_sourceSafe : {ident f.name}.safe{String.join (names.map (" " ++ ·))})\n" ++
    s!"    (_entrySafe : {ident f.name}.entrySafe _sourceHeap {args} = true) :\n" ++
    s!"    Adequacy.WrappedSourceMutatesFrom _root_.{namespace_}.source _root_.{namespace_}.Wrapper.source\n" ++
    s!"      {compact f.name} _sourceHeap {args} {layout} (.ref _sourceAddress) ({call}).2.1 := by\n" ++
    s!"  exact Adequacy.transfer_mutation EntryGuards.{ident f.name}.certificate\n" ++
    s!"    ({theoremName}{String.join (names.map (" " ++ ·))} _sourceHeap _sourceAddress _sourceFootprint _sourceInput _sourceSafe) _entrySafe\n\n"

/-- Emit witnesses only for mutation shapes covered by the operational proof. -/
def sourceTheorem (namespace_ : String) (f : Ariadne.Function) (core : Core.Function)
    (params : String) (names : List String) (publicAlias : Bool) : Option String :=
  (mapSourceTheorem namespace_ f core params names publicAlias).orElse fun _ =>
    (arraySourceTheorem namespace_ f core params names publicAlias).orElse fun _ =>
      fieldSourceTheorem namespace_ f core params names publicAlias

end Ariadne.Shallow.ProjectionEmit
