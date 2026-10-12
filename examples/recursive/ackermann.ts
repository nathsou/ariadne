// Nested recursion stresses argument evaluation and frame restoration.
export function ackermann(m: bigint, n: bigint): bigint {
  if (m <= 0n) { return n + 1n; }
  if (n <= 0n) { return ackermann(m - 1n, 1n); }
  return ackermann(m - 1n, ackermann(m, n - 1n));
}
