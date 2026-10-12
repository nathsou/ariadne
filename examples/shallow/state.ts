export function bump(store: Map<string, bigint>, key: string): bigint {
  const next = (store.get(key) ?? 0n) + 1n;
  store.set(key, next);
  return next;
}

export function count(store: Map<string, bigint>, keys: readonly string[]): void {
  for (const key of keys) { store.set(key, (store.get(key) ?? 0n) + 1n); }
}

export function transfer(source: Map<string, bigint>, target: Map<string, bigint>, key: string): void {
  const value = source.get(key);
  if (value === undefined) { return; }
  source.delete(key);
  target.set(key, value);
}

export function scoped(store: Map<string, bigint>): bigint {
  store.set('original', 1n);
  {
    const local = new Map<string, bigint>();
    local.set('local', 2n);
    return local.get('local') ?? 0n;
  }
}

export function early(store: Map<string, bigint>, skip: boolean): void {
  if (skip) { return; }
  store.set('updated', 1n);
}

export function read(store: Map<string, bigint>, key: string): bigint {
  return store.get(key) ?? 0n;
}

export function twice(store: Map<string, bigint>, key: string): bigint {
  const first = bump(store, key);
  const second = bump(store, key);
  return first + second;
}

export function localCalls(key: string): bigint {
  const store = new Map<string, bigint>();
  count(store, [key, key]);
  return bump(store, key);
}

export function swapInto(source: Map<string, bigint>, target: Map<string, bigint>, key: string): bigint {
  transfer(source, target, key);
  return target.get(key) ?? 0n;
}

export function fromFresh(key: string): bigint {
  return bump(new Map<string, bigint>(), key);
}

export function append(values: bigint[], items: readonly bigint[]): void {
  for (const item of items) { values.push(item); }
}

export function appendLength(values: bigint[], items: readonly bigint[]): number {
  append(values, items);
  return values.length;
}

export function addAll(values: Set<bigint>, items: readonly bigint[]): void {
  for (const item of items) { values.add(item); }
}

export function until(store: Map<string, bigint>, keys: readonly string[], stop: string): bigint {
  let total = 0n;
  for (const key of keys) {
    if (key === stop) { return total; }
    bump(store, key);
    total += 1n;
  }
  return total;
}

export function pureCopy(values: bigint[]): bigint[] { return values.slice(); }

export function copyCaller(values: bigint[]): bigint[] {
  const result = pureCopy(values);
  result.push(9n);
  return result;
}
