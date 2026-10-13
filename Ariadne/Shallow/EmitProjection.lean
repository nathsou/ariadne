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


/-- Emit witnesses only for mutation shapes covered by the operational proof. -/
def sourceTheorem (namespace_ : String) (f : Ariadne.Function) (core : Core.Function)
    (params : String) (names : List String) (publicAlias : Bool) : Option String :=
  (mapSourceTheorem namespace_ f core params names publicAlias).orElse fun _ =>
    arraySourceTheorem namespace_ f core params names publicAlias

end Ariadne.Shallow.ProjectionEmit
