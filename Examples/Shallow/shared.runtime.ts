// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.
export function nested(flag: boolean, x: bigint): bigint {
  if (flag) { { const y = x + 1n; x = y * 2n; } }
  else { x -= 1n; }
  return x * 3n;
}
export function flattened(flag: boolean, x: bigint): bigint {
  { x = x + 1n; }
  if (flag) { x = x * 2n; } else { x = x - 2n; }
  return x;
}
export function nestedFlattened(flag: boolean, x: bigint): bigint {
  if (flag) {
    { x = x + 1n; }
    { const y = x * 2n; x = y; }
  } else { x = x - 1n; }
  return x;
}
export function early(flag: boolean, x: bigint): bigint {
  if (flag) { { const y = x + 1n; x = y; } return x; }
  { x = x - 1n; }
  return x;
}
export function empty(x: bigint): bigint { {} { {} } return x; }
export function greater(x: bigint, y: bigint): boolean { return x > y; }
export function numberGreater(x: number, y: number): boolean { return x >= y; }
export function stringGreater(x: string, y: string): boolean { return x > y; }
