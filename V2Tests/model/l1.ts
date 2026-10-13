// Model validation (L1): records, spreads, field reads, nullish operators, switch.
interface Point { x: bigint; y: bigint; label?: string }

function point(x: bigint, y: bigint): Point {
  return { x, y };
}

export function t_record(): Point {
  return { y: 2n, x: 1n, label: "p" };
}

export function t_spread_override(): Point {
  const p = point(1n, 2n);
  return { ...p, x: 5n, label: "moved" };
}

export function t_spread_position(): Point {
  // An overridden key keeps its first position.
  const p = { x: 1n, y: 2n };
  return { y: 0n, ...p };
}

export function t_spread_nullish(): Point {
  const p = { x: 1n, y: 2n };
  return { ...p, ...undefined, ...null };
}

export function t_missing_field(): string | undefined {
  const p = point(1n, 2n);
  return p.label;
}

export function t_undefined_field(): Point {
  return { x: 1n, y: 2n, label: undefined };
}

export function t_loose_null(): boolean[] {
  const a = undefined;
  const b = null;
  const c = "x";
  return [a == null, b == null, c == null, a != null, c != null];
}

export function t_coalesce(): string[] {
  const a = undefined;
  const b = null;
  const c = "";
  return [a ?? "a", b ?? "b", c ?? "c"];
}

type Fact = { kind: "unopened" } | { kind: "damaged" } | { kind: "opened"; written: bigint; kid?: string };

function describe(f: Fact): string {
  switch (f.kind) {
    case "unopened":
      return "u";
    case "damaged":
      return "d";
    case "opened": {
      const k = f.kid ?? "-";
      return "o" + k;
    }
  }
  return "?";
}

export function t_switch_union(): string[] {
  return [describe({ kind: "unopened" }), describe({ kind: "damaged" }), describe({ kind: "opened", written: 1n }),
    describe({ kind: "opened", written: 1n, kid: "k" })];
}

function fallthrough(n: bigint): string {
  let s = "";
  switch (n) {
    case 1n:
      s = s + "a";
    case 2n:
      s = s + "b";
      break;
    default:
      s = s + "z";
    case 3n:
      s = s + "c";
  }
  return s;
}

export function t_switch_fallthrough(): string[] {
  return [fallthrough(1n), fallthrough(2n), fallthrough(3n), fallthrough(4n)];
}

type Choice = { ok: true; value: bigint } | { ok: false; reason: string };

function choose(n: bigint): Choice {
  if (n > 0n) return { ok: true, value: n };
  return { ok: false, reason: "non-positive" };
}

export function t_bool_tag(): Choice[] {
  return [choose(3n), choose(-1n)];
}

function optional(a: bigint, b?: bigint): bigint {
  if (b == null) return a;
  return a + b;
}

export function t_optional_params(): bigint[] {
  return [optional(1n), optional(1n, 2n), optional(1n, undefined)];
}

export function fault_prototype_read(): string | undefined {
  const p = point(1n, 2n);
  return p.toString;
}

export function fault_identity(): boolean {
  const p = point(1n, 2n);
  return p === p;
}
