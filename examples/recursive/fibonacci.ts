export function fibonacci(count: bigint): bigint {
  if (count <= 0n) { return 0n; }
  if (count === 1n) { return 1n; }
  return fibonacci(count - 1n) + fibonacci(count - 2n);
}
