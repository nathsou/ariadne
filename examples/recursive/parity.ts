// Forward references and mutual recursion share the same linked function table.
export function parity(count: bigint): boolean {
  if (count < 0n) { count = -count; }
  return isEven(count);
}
function isEven(count: bigint): boolean {
  if (count === 0n) { return true; }
  return isOdd(count - 1n);
}
function isOdd(count: bigint): boolean {
  if (count === 0n) { return false; }
  return isEven(count - 1n);
}
