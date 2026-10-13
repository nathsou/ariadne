import Ariadne.Ownership.Wrap
import Ariadne.Ownership.Forest
import Ariadne.Ownership.MethodGuard

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Tests.EntryGuards
open Ariadne Ownership

private def plan (source : String) : Checked (List ArgumentCheck) := do
  let program ← frontend source
  let some function := program.functions.find? (·.name == "f")
    | Check.error "A2003" "missing fixture function" {}
  entryPlan program function

theorem flat_borrows_compare_roots :
    plan "export function f(xs: bigint[], ys: readonly bigint[]): void { xs.push(1n); }" =
      .ok [⟨0, 1, .root, .root, none⟩] := by kernel_rfl

theorem immutable_arguments_need_no_guard :
    plan "export function f(xs: readonly bigint[], ys: readonly bigint[]): bigint { return 0n; }" =
      .ok [] := by kernel_rfl

theorem argument_inside_other_argument_is_deep :
    plan "export function f(rows: readonly bigint[][], xs: bigint[]): void { xs.push(1n); }" =
      .ok [⟨0, 1, .deep, .root, none⟩] := by kernel_rfl

theorem observation_inside_mutated_argument_is_deep :
    plan "export function f(rows: bigint[][], xs: readonly bigint[]): void { rows.push([1n]); }" =
      .ok [⟨0, 1, .deep, .root, none⟩] := by kernel_rfl

theorem encapsulated_fields_are_not_nested :
    plan "class Box { private items: bigint[] = []; } export function f(box: Box, xs: bigint[]): void { xs.push(1n); }" =
      .ok [⟨0, 1, .root, .root, none⟩] := by kernel_rfl

theorem class_method_writes_are_guarded :
    plan "class Box { private items: bigint[] = []; add(x: bigint): void { this.items.push(x); } } export function f(a: Box, b: Box): void { a.add(1n); }" =
      .ok [⟨0, 1, .root, .root, none⟩] := by kernel_rfl

theorem public_fields_are_nested :
    plan "class Box { items: bigint[] = []; } export function f(box: Box, xs: bigint[]): void { xs.push(1n); }" =
      .ok [⟨0, 1, .deep, .root, none⟩] := by kernel_rfl

theorem transitive_record_containment_is_deep :
    plan "type Box = { readonly rows: readonly bigint[][] }; export function f(box: Box, xs: bigint[]): void { xs.push(1n); }" =
      .ok [⟨0, 1, .deep, .root, none⟩] := by kernel_rfl

private def roots : ArgumentCheck := ⟨0, 1, .root, .root, none⟩
private def nested : ArgumentCheck := ⟨0, 1, .deep, .root, none⟩
private def noFunctions : Program := {functions := []}

theorem root_alias_throws :
    checkedApply noFunctions [roots] 0 {heap := [.array []]} "implementation" [.ref 0, .ref 0] =
      .error (.typeError "overlapping borrowed arguments") := by kernel_rfl

theorem deep_alias_throws :
    checkedApply noFunctions [nested] 0 {heap := [.array [.ref 1], .array []]}
      "implementation" [.ref 0, .ref 1] =
      .error (.typeError "overlapping borrowed arguments") := by kernel_rfl

theorem passing_does_not_copy_or_change_arguments :
    checkedApply noFunctions [nested] 7 {heap := [.array [.ref 1], .array [], .array []]}
      "implementation" [.ref 0, .ref 2] =
      apply noFunctions 7 {heap := [.array [.ref 1], .array [], .array []]}
        (.function "implementation") [.ref 0, .ref 2] := by kernel_rfl

theorem optional_missing_arguments_do_not_overlap :
    entrySafe noFunctions [roots] [] [.undefined, .undefined] = true := by kernel_rfl

theorem cyclic_search_terminates :
    containsReference noFunctions [.record [("back", .ref 0)]] 1 1 [] (.ref 0) = .ok false := by
  kernel_rfl

theorem dangling_reference_fails_before_implementation :
    checkedApply noFunctions [nested] 0 {heap := [.array [.ref 4], .array []]}
      "implementation" [.ref 0, .ref 1] =
      .error (.typeError "entry guard encountered a dangling reference") := by kernel_rfl

theorem method_alias_fails_before_body :
    checkedMethodApply noFunctions [⟨1, 2, .root, .root, none⟩] 0
      {heap := [.instance_ "GuardedBox" [], .array []]} 0 "append" [.ref 1, .ref 1] =
      .error (.typeError "overlapping borrowed arguments") := by kernel_rfl

end Tests.EntryGuards
