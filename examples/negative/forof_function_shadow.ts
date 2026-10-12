// expected: A3004
function helper(): bigint { return 1n; }
function demo(values: readonly bigint[]): bigint {
  let total = 0n;
  for (const helper of values) { total += helper(); }
  return total;
}
