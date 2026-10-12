// Returns at most the requested number of steps; no Collatz conjecture is assumed.
export function collatz(value: bigint, limit: bigint): bigint {
  let steps = 0n;
  while (value > 1n && steps < limit) {
    value = next(value);
    steps = steps + 1n;
  }
  return steps;
}
function next(value: bigint): bigint {
  if (value % 2n === 0n) { return value / 2n; }
  return 3n * value + 1n;
}
