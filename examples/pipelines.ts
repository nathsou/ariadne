export function demo(): bigint {
  const values = [1n, 2n, 3n, 4n, 5n, 6n];
  const squares = values.map((x: bigint) => x * x);
  const selected = squares.filter((x: bigint) => x % 2n === 0n);
  return selected.reduce((sum: bigint, x: bigint) => sum + x, 0n);
}

export function capturedAccumulator(): bigint {
  const values = [2n, 3n, 5n, 7n];
  let product = 1n;
  values.forEach((x: bigint) => { product *= x; });
  return product;
}
