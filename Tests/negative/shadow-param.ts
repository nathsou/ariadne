// expect: A2004
export function f(x: bigint): bigint {
  if (x > 0n) {
    const x = 1n;
    return x;
  }
  return x;
}
