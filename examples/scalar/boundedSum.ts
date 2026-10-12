// Continue must execute the for-loop update; break must skip it.
export function boundedSum(limit: bigint, stop: bigint): bigint {
  let total = 0n;
  for (let i = 0n; i < limit; i = i + 1n) {
    if (i >= stop) { break; }
    if (i % 2n === 0n) { continue; }
    total = total + i;
  }
  return total;
}
