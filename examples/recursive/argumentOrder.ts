// The first failing argument determines the runtime error.
export function argumentOrder(conversionFirst: boolean): bigint {
  if (conversionFirst) { return add(BigInt(0.5), 1n / 0n); }
  return add(1n / 0n, BigInt(0.5));
}
function add(left: bigint, right: bigint): bigint {
  return left + right;
}
