// Recursive counting, including the zero-iteration behavior of negative inputs.
export function countdown(count: bigint): bigint {
  if (count <= 0n) { return 0n; }
  return 1n + countdown(count - 1n);
}
