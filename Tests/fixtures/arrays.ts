// Integer-mode numbers, arrays, callbacks, sorting.
export interface Entry { id: number; size: number; name: string; tags: readonly string[] }

export function total(a: number, b: number): number {
  return a + b * 2;
}

export function negate(x: number): number {
  return -x;
}

export function clampIndex(i: number, n: number): number {
  if (i < 0) return 0;
  if (i >= n) return n - 1;
  return i;
}

export function count(es: readonly Entry[]): number {
  return es.length;
}

export function sizes(es: readonly Entry[]): number[] {
  return es.map((e) => e.size);
}

export function named(es: readonly Entry[], name: string): Entry | undefined {
  return es.find((e) => e.name === name);
}

export function tagged(es: readonly Entry[], tag: string): Entry[] {
  return es.filter((e) => e.tags.includes(tag));
}

export function anyLarge(es: readonly Entry[], limit: number): boolean {
  return es.some((e) => e.size > limit);
}

export function allNamed(es: readonly Entry[]): boolean {
  return es.every((e) => e.name.length > 0);
}

export function bySize(es: readonly Entry[]): Entry[] {
  return es.toSorted((a, b) => a.size - b.size);
}

export function byName(es: readonly Entry[]): Entry[] {
  return es.toSorted((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}

export function ids(es: readonly Entry[]): number[] {
  return [0, ...es.map((e) => e.id), -1];
}

export function firstName(es: readonly Entry[]): string {
  const e = es[0];
  if (e == null) return '';
  return e.name;
}

export function grow(es: readonly Entry[], by: number): Entry[] {
  return es.map((e) => ({ ...e, size: e.size + by }));
}

export function signs(xs: readonly number[]): string[] {
  return xs.map((x) => (x > 0 ? 'pos' : x === 0 ? 'zero' : 'neg'));
}

export function scaled(xs: readonly number[], k: number): number[] {
  return xs.filter((x) => x !== 0).map((x) => x * k);
}

export function totalOf(es: readonly Entry[]): number {
  return total(count(es), 1);
}

function isLarge(e: Entry): boolean {
  return e.size > 100;
}

function bySizeDesc(a: Entry, b: Entry): number {
  if (a.size !== b.size) return a.size > b.size ? -1 : 1;
  return 0;
}

export function large(es: readonly Entry[]): Entry[] {
  return es.filter(isLarge);
}

export function ranked(es: readonly Entry[]): Entry[] {
  return es.toSorted(bySizeDesc);
}

export function flags(es: readonly Entry[]): boolean[] {
  return es.map(() => false);
}

export function summaries(es: readonly Entry[]): Entry[] {
  return es.map((e) => ({ id: e.id, size: e.size + 1, name: e.name, tags: [] }));
}
