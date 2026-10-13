// L1: records, spreads, optionals, narrowing, literal and tagged unions.
export interface Point { x: bigint; y: bigint; label?: string }

export type Recovery = 'none' | 'ok' | 'legacy' | 'bad';

export type Fact =
  | { kind: 'unopened' }
  | { kind: 'damaged' }
  | { kind: 'opened'; written: bigint; recovery: Recovery; kid?: string };

export type Choice = { ok: true; value: bigint } | { ok: false; reason: string };

export function origin(): Point {
  return { x: 0n, y: 0n };
}

export function moved(p: Point, dx: bigint): Point {
  return { ...p, x: p.x + dx, label: 'moved' };
}

export function labelOf(p: Point): string {
  return p.label ?? 'unnamed';
}

export function hasLabel(p: Point): boolean {
  const l = p.label;
  if (l == null) return false;
  return l !== '';
}

export function describe(f: Fact): string {
  switch (f.kind) {
    case 'unopened':
      return 'u';
    case 'damaged':
      return 'd';
    case 'opened': {
      const k = f.kid;
      const suffix = k == null ? '-' : k;
      if (f.recovery === 'bad') {
        return 'o!' + suffix;
      }
      return 'o' + suffix;
    }
  }
}

export function trusted(f: Fact): boolean {
  switch (f.kind) {
    case 'unopened':
      return false;
    case 'damaged':
      return false;
    case 'opened':
      return f.recovery !== 'bad' && f.recovery !== 'legacy';
  }
}

export function choose(n: bigint, floor?: bigint | null): Choice {
  if (floor != null) {
    if (n < floor) return { ok: false, reason: 'older' };
  }
  if (n > 0n) return { ok: true, value: n };
  return { ok: false, reason: 'non-positive' };
}

export function orDefault(c: Choice): bigint {
  switch (c.ok) {
    case true:
      return c.value;
    case false:
      return -1n;
  }
}

export function pick(a: Point, b: Point, preferA: boolean): Point {
  const chosen = preferA ? a : b;
  return { ...chosen, label: chosen.label ?? 'picked' };
}
