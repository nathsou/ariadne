export function positiveDoubled(xs: readonly bigint[], delta: bigint): bigint[] {
  return xs.filter((x: bigint) => x >= 0n).map((x: bigint) => x * 2n + delta);
}

export function total(xs: readonly bigint[]): bigint {
  return xs.reduce((acc: bigint, x: bigint) => acc + x, 0n);
}
