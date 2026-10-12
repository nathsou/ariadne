// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.
function __ariadne0_contains(target: object, value: unknown, seen: Set<object> = new Set<object>()): boolean {
  if (value === target) { return true; }
  if (value === null || typeof value !== 'object' || seen.has(value)) { return false; }
  seen.add(value);
  if (Array.isArray(value)) {
    for (const item of value) { if (__ariadne0_contains(target, item, seen)) { return true; } }
    return false;
  }
  if (value instanceof Map) {
    for (const item of value.values()) { if (__ariadne0_contains(target, item, seen)) { return true; } }
    return false;
  }
  if (value instanceof Set) { return false; }
  for (const key of Object.keys(value)) {
    if (__ariadne0_contains(target, (value as { [key: string]: unknown })[key], seen)) { return true; }
  }
  return false;
}

export function grow(rows: readonly bigint[][], items: bigint[]): void {
  if (rows !== null && typeof rows === 'object' && items !== null && typeof items === 'object' && ((rows as object) === (items as object) || __ariadne0_contains(items, rows))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  return __ariadne0_grow(rows, items);
}

function __ariadne0_grow(rows: readonly bigint[][], items: bigint[]): void {
  items.push(1n);
}
