// Each recursive call has a fresh parameter cell and local total.
export function localFrames(count: bigint): bigint {
  let total = count;
  if (count > 0n) {
    total = total + localFrames(count - 1n);
  }
  return total + count;
}
