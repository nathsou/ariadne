export function grow(rows: readonly bigint[][], items: bigint[]): void {
  items.push(1n);
}

export function outer(rows: bigint[][], items: readonly bigint[]): void {
  rows.push([2n]);
}

export function mapped(rows: Map<string, bigint[]>, items: bigint[]): void {
  items.push(3n);
}

export function flat(left: bigint[], right: readonly bigint[]): void {
  left.push(4n);
}

export function observations(left: readonly bigint[], right: readonly bigint[]): bigint {
  return 5n;
}

export class Box {
  private items: bigint[] = [0n];
  add(value: bigint): void { this.items.push(value); }
}

export function encapsulated(left: Box, right: Box): void { left.add(6n); }

export class PublicBox {
  items: bigint[] = [0n];
}

export function exposed(box: PublicBox, items: bigint[]): void { items.push(7n); }

// Generated helper names must not shadow source bindings.
export function names(__ariadne0_contains: bigint[], other: readonly bigint[]): void {
  __ariadne0_contains.push(8n);
}
