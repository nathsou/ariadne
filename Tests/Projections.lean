import Ariadne

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Tests.Projections
open Ariadne

theorem map_statement :
    (frontend "function f(m: Map<string, bigint[]>, k: string, x: bigint): void { m.get(k)!.push(x); }").isOk = true := by kernel_rfl

theorem array_statement :
    (frontend "function f(rows: bigint[][], i: number, x: bigint): void { rows[i].push(x); }").isOk = true := by kernel_rfl

theorem scalar_element_update :
    (frontend "function f(rows: number[], i: number): void { rows[i]++; }").isOk = true := by kernel_rfl

theorem field_increment :
    (frontend "type Row = { count: number }; function f(rows: Row[], i: number): void { rows[i].count++; }").isOk = true := by kernel_rfl

theorem compound_field_update :
    (frontend "type Row = { count: number }; function f(rows: Row[], i: number, x: number): void { rows[i].count += x; }").isOk = true := by kernel_rfl

theorem second_path_refused :
    (frontend "function f(rows: bigint[][], i: number): void { rows[i].push(rows[0]![0] ?? 0n); }").isOk = false := by kernel_rfl

theorem container_read_during_projection_refused :
    (frontend "function f(rows: number[][], i: number): void { rows[i].push(rows.length); }").isOk = false := by kernel_rfl

theorem impure_key_refused :
    (frontend "function index(): number { return 0; } function f(rows: bigint[][]): void { rows[index()].push(1n); }").isOk = false := by kernel_rfl

theorem impure_argument_refused :
    (frontend "function value(): bigint { return 1n; } function f(rows: bigint[][]): void { rows[0].push(value()); }").isOk = false := by kernel_rfl

theorem readonly_container_refused :
    (frontend "function f(rows: readonly bigint[][]): void { rows[0].push(1n); }").isOk = false := by kernel_rfl

theorem readonly_element_refused :
    (frontend "type Row = readonly bigint[]; function f(rows: Row[]): void { rows[0].push(1n); }").isOk = false := by kernel_rfl

theorem lifetime_does_not_extend :
    (frontend "function f(rows: bigint[][]): void { rows[0].push(1n); const row = rows[0]; row.push(2n); }").isOk = false := by kernel_rfl

private def simultaneousBase :=
  "type Row = { count: bigint }; function swap(a: Row, b: Row): void { const saved = a.count; a.count = b.count; b.count = saved; } "

theorem simultaneous_array_entry :
    (frontend (simultaneousBase ++ "export function f(rows: Row[], i: number, j: number): void { swap(rows[i], rows[j]); }")).isOk = true := by kernel_rfl

theorem simultaneous_map_entry :
    (frontend (simultaneousBase ++ "export function f(rows: Map<string, Row>, i: string, j: string): void { swap(rows.get(i)!, rows.get(j)!); }")).isOk = true := by kernel_rfl

theorem simultaneous_number_map_entry :
    (frontend (simultaneousBase ++ "export function f(rows: Map<number, Row>, i: number, j: number): void { swap(rows.get(i)!, rows.get(j)!); }")).isOk = true := by kernel_rfl

theorem simultaneous_nonentry_refused :
    (frontend (simultaneousBase ++ "function f(rows: Row[], i: number, j: number): void { swap(rows[i], rows[j]); }")).isOk = false := by kernel_rfl

theorem simultaneous_additional_statement_refused :
    (frontend (simultaneousBase ++ "export function f(rows: Row[], i: number, j: number): void { swap(rows[i], rows[j]); const count = rows.length; }")).isOk = false := by kernel_rfl

theorem simultaneous_impure_key_refused :
    (frontend (simultaneousBase ++ "function key(): number { return 0; } export function f(rows: Row[], j: number): void { swap(rows[key()], rows[j]); }")).isOk = false := by kernel_rfl

theorem simultaneous_readonly_element_refused :
    (frontend (simultaneousBase ++ "type View = readonly Row; export function f(rows: View[], i: number, j: number): void { swap(rows[i], rows[j]); }")).isOk = false := by kernel_rfl

theorem simultaneous_internal_entry_call_refused :
    (frontend (simultaneousBase ++ "export function f(rows: Row[], i: number, j: number): void { swap(rows[i], rows[j]); } export function g(rows: Row[], i: number): void { f(rows, i, i); }")).isOk = false := by kernel_rfl

theorem simultaneous_zero_guard :
    Ownership.entrySafe {functions := []} [{left := 0, right := 1, leftTraversal := .root, rightTraversal := .root, projection := some .array}]
      [] [.number (Float.Model.ofNat 0), .number (-(Float.Model.ofNat 0))] = false := by kernel_rfl

theorem simultaneous_nan_map_guard :
    Ownership.entrySafe {functions := []} [{left := 0, right := 1, leftTraversal := .root, rightTraversal := .root, projection := some .map}]
      [] [.number Float.Model.nan, .number Float.Model.nan] = false := by kernel_rfl

end Tests.Projections
