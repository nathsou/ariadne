// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.
function __ariadne1_contains(target: object, value: unknown, seen: Set<object> = new Set<object>()): boolean {
  if (value === target) { return true; }
  if (value === null || typeof value !== 'object' || seen.has(value)) { return false; }
  seen.add(value);
  if (Array.isArray(value)) {
    for (const item of value) { if (__ariadne1_contains(target, item, seen)) { return true; } }
    return false;
  }
  if (value instanceof Map) {
    for (const item of value.values()) { if (__ariadne1_contains(target, item, seen)) { return true; } }
    return false;
  }
  if (value instanceof Set) { return false; }
  if (value instanceof Box) {
    return false;
  }
  if (value instanceof PublicBox) {
    if (__ariadne1_contains(target, value["items"], seen)) { return true; }
    return false;
  }
  if (value instanceof GuardedBox) {
    return false;
  }
  for (const key of Object.keys(value)) {
    if (__ariadne1_contains(target, (value as { [key: string]: unknown })[key], seen)) { return true; }
  }
  return false;
}

export function grow(rows: readonly bigint[][], items: bigint[]): void {
  if (rows !== null && typeof rows === 'object' && items !== null && typeof items === 'object' && ((rows as object) === (items as object) || __ariadne1_contains(items, rows))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  return __ariadne1_grow(rows, items);
}

function __ariadne1_grow(rows: readonly bigint[][], items: bigint[]): void {
  items.push(1n);
}

export function outer(rows: bigint[][], items: readonly bigint[]): void {
  if (rows !== null && typeof rows === 'object' && items !== null && typeof items === 'object' && ((rows as object) === (items as object) || __ariadne1_contains(items, rows))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  return __ariadne1_outer(rows, items);
}

function __ariadne1_outer(rows: bigint[][], items: readonly bigint[]): void {
  rows.push([2n]);
}

export function mapped(rows: Map<string, bigint[]>, items: bigint[]): void {
  if (rows !== null && typeof rows === 'object' && items !== null && typeof items === 'object' && ((rows as object) === (items as object) || __ariadne1_contains(items, rows))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  return __ariadne1_mapped(rows, items);
}

function __ariadne1_mapped(rows: Map<string, bigint[]>, items: bigint[]): void {
  items.push(3n);
}

export function flat(left: bigint[], right: readonly bigint[]): void {
  if (left !== null && typeof left === 'object' && right !== null && typeof right === 'object' && ((left as object) === (right as object))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  return __ariadne1_flat(left, right);
}

function __ariadne1_flat(left: bigint[], right: readonly bigint[]): void {
  left.push(4n);
}

export function observations(left: readonly bigint[], right: readonly bigint[]): bigint {
  return 5n;
}

export class Box {
  private items: bigint[] = [0n];
  add(value: bigint): void { this.items.push(value); }
}

export function encapsulated(left: Box, right: Box): void {
  if (left !== null && typeof left === 'object' && right !== null && typeof right === 'object' && ((left as object) === (right as object))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  return __ariadne1_encapsulated(left, right);
}

function __ariadne1_encapsulated(left: Box, right: Box): void { left.add(6n); }

export class PublicBox {
  items: bigint[] = [0n];
}

export function exposed(box: PublicBox, items: bigint[]): void {
  if (box !== null && typeof box === 'object' && items !== null && typeof items === 'object' && ((box as object) === (items as object) || __ariadne1_contains(items, box))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  return __ariadne1_exposed(box, items);
}

function __ariadne1_exposed(box: PublicBox, items: bigint[]): void { items.push(7n); }

// Generated helper names must not shadow source bindings.
export function names(__ariadne0_contains: bigint[], other: readonly bigint[]): void {
  if (__ariadne0_contains !== null && typeof __ariadne0_contains === 'object' && other !== null && typeof other === 'object' && ((__ariadne0_contains as object) === (other as object))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  return __ariadne1_names(__ariadne0_contains, other);
}

function __ariadne1_names(__ariadne0_contains: bigint[], other: readonly bigint[]): void {
  __ariadne0_contains.push(8n);
}

export class GuardedBox {
  private count = 0n;
  append(left: bigint[], right: readonly bigint[]): void {
  if (this !== null && typeof this === 'object' && left !== null && typeof left === 'object' && ((this as object) === (left as object))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  if (left !== null && typeof left === 'object' && right !== null && typeof right === 'object' && ((left as object) === (right as object))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  const __ariadne1_implementation = () => { left.push(9n); };
  return __ariadne1_implementation();
}
}
