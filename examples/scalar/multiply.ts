// Repeated addition: negative counts perform zero iterations.
export function multiply(value: bigint, count: bigint): bigint {
  let total = 0n;
  while (count > 0n) {
    total = total + value;
    count = count - 1n;
  }
  return total;
}
