// `let`, assignment, loops, break and continue.
export interface Item { id: number; size: number; tags: readonly string[] }

export type Shape = { kind: 'circle'; r: number } | { kind: 'square'; side: number };

export function sum(xs: readonly number[]): number {
  let total = 0;
  for (const x of xs) {
    total += x;
  }
  return total;
}

export function firstLarge(items: readonly Item[], limit: number): Item | undefined {
  for (const it of items) {
    if (it.size > limit) return it;
  }
  return undefined;
}

export function indexOf(xs: readonly string[], target: string): number {
  for (const [i, x] of xs.entries()) {
    if (x === target) return i;
  }
  return -1;
}

export function countTagged(items: readonly Item[], tag: string): number {
  let n = 0;
  for (const it of items) {
    if (!it.tags.includes(tag)) continue;
    n = n + 1;
  }
  return n;
}

export function prefixUntil(xs: readonly number[], stop: number): number[] {
  let out: number[] = [];
  for (const x of xs) {
    if (x === stop) break;
    out = [...out, x];
  }
  return out;
}

export function largest(items: readonly Item[]): Item | undefined {
  let best: Item | undefined = undefined;
  for (const it of items) {
    if (best == null) {
      best = it;
      continue;
    }
    if (it.size > best.size) best = it;
  }
  return best;
}

export function classify(xs: readonly number[]): string {
  let pos = 0;
  let neg = 0;
  for (const x of xs) {
    if (x > 0) pos += 1;
    else if (x < 0) neg += 1;
  }
  if (pos > neg) return 'pos';
  if (neg > pos) return 'neg';
  return 'even';
}

export function bump(n: number): number {
  n = n + 1;
  return n * 2;
}

export function grid(rows: readonly number[][]): number {
  let total = 0;
  for (const row of rows) {
    for (const [j, v] of row.entries()) {
      if (j > 2) break;
      total = total + v;
    }
  }
  return total;
}

export function perimeters(shapes: readonly Shape[]): number {
  let t = 0;
  for (const sh of shapes) {
    switch (sh.kind) {
      case 'circle':
        t = t + 6 * sh.r;
        break;
      case 'square':
        t = t + 4 * sh.side;
        break;
    }
  }
  return t;
}

export function steps(n: number): number {
  let count = 0;
  let k = n;
  for (const _ of [1, 2, 3, 4, 5, 6, 7, 8]) {
    if (k <= 1) break;
    k = k > 100 ? k - 100 : k - 1;
    count++;
  }
  return count;
}

export function score(a: number, b: number): number {
  let s = 0;
  if (a > 0) s = s + 1;
  else s = s - 1;
  if (b > 0) s = s * 2;
  return s;
}

/** A counted loop over `0 … m-1` with a constant bound (at most 1,000, so the test's huge
inputs stay quick in JavaScript). */
export function triangle(n: number, cap: number): number {
  const m = n < 1000 ? n : 1000;
  let t = 0;
  for (let i = 0; i < m; i++) {
    if (i > cap) break;
    if (i === 3) continue;
    t = t + i;
  }
  return t;
}
