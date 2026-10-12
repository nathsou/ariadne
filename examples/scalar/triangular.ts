export function triangular(count: bigint): bigint {
  let total = 0n;
  for (let i = 1n; i <= count; i = i + 1n) {
    total = total + i;
  }
  return total;
}
