// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.
export function histogram(xs: readonly string[]): Map<string, bigint> {
  const counts = new Map<string, bigint>();
  for (const x of xs) { counts.set(x, (counts.get(x) ?? 0n) + 1n); }
  return counts;
}

export function ordered(xs: readonly string[]): string[] {
  const values = new Map<string, bigint>();
  for (const x of xs) { values.set(x, 1n); }
  values.delete('remove');
  values.set('remove', 2n);
  return [...values.keys()];
}

export function numericSet(xs: readonly number[]): number[] {
  const values = new Set<number>();
  for (const x of xs) { values.add(x); }
  return [...values];
}

export function numericMap(xs: readonly number[]): Map<number, bigint> {
  const values = new Map<number, bigint>();
  for (const x of xs) { values.set(x, (values.get(x) ?? 0n) + 1n); }
  return values;
}

export function flags(xs: readonly boolean[]): bigint {
  const values = new Map<boolean, bigint>();
  for (const x of xs) { values.set(x, (values.get(x) ?? 0n) + 1n); }
  return values.get(true) ?? 0n;
}

export function unique(xs: readonly bigint[], remove: bigint): bigint[] {
  const values = new Set<bigint>();
  for (const x of xs) { values.add(x); }
  values.delete(remove);
  return [...values.values()];
}

export function entries(xs: readonly string[]): bigint {
  const values = new Map<string, bigint>();
  for (const x of xs) { values.set(x, (values.get(x) ?? 0n) + 1n); }
  let total = 0n;
  for (const entry of values) {
    if (entry[0] !== 'skip') { total += entry[1]; }
  }
  return total;
}

export function setEntries(xs: readonly bigint[]): bigint {
  const values = new Set<bigint>();
  for (const x of xs) { values.add(x); }
  let total = 0n;
  for (const entry of values.entries()) { total += entry[0] + entry[1]; }
  return total;
}

export function collect(xs: readonly bigint[]): bigint[] {
  const out: bigint[] = [];
  for (const x of xs) {
    if (x < 0n) { continue; }
    out.push(x + 1n);
  }
  return out;
}

export function clear(xs: readonly string[], reset: boolean): number {
  const values = new Map<string, bigint>();
  const seen = new Set<string>();
  for (const x of xs) { values.set(x, 1n); seen.add(x); }
  if (reset) { values.clear(); seen.clear(); }
  return values.size + seen.size;
}

export function read(values: ReadonlyMap<string, bigint>, key: string): bigint | undefined {
  return values.get(key);
}

export function readDefault(values: ReadonlyMap<string, bigint>, key: string): bigint {
  return read(values, key) ?? 9n;
}

export function numericHas(xs: readonly number[], remove: number, query: number): boolean {
  const values = new Set<number>();
  for (const x of xs) { values.add(x); }
  values.delete(remove);
  return values.has(query);
}

export function numericDelete(xs: readonly number[], remove: number): number[] {
  const values = new Map<number, bigint>();
  for (const x of xs) { values.set(x, 1n); }
  values.delete(remove);
  return [...values.keys()];
}

export function nestedValues(key: string): bigint[] {
  const values = new Map<string, bigint[]>();
  values.set('a', [1n, 2n]);
  return (values.get(key) ?? []).slice();
}

export function entryValues(xs: readonly string[]): bigint[] {
  const values = new Map<string, bigint>();
  for (const x of xs) { values.set(x, (values.get(x) ?? 0n) + 1n); }
  return [...values].map((entry: [string, bigint]) => entry[1]);
}

export function entrySizes(xs: readonly string[]): number[] {
  const values = new Map<string, bigint>();
  for (const x of xs) { values.set(x, 1n); }
  return [...values.entries()].map((entry: [string, bigint]) => entry.length);
}

export function tupleSize(): number {
  const pair: [bigint, bigint] = [1n, 2n];
  return pair.length;
}
