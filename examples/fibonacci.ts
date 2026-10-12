export function fibonacci(n: bigint): bigint {
  let previous = 0n;
  let current = 1n;
  let index = 0n;
  while (index < n) {
    const next = previous + current;
    previous = current;
    current = next;
    index += 1n;
  }
  return previous;
}

export function demo(): bigint {
  return fibonacci(20n);
}
