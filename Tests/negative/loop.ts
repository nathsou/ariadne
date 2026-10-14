// expect: A1001
export function f(x: bigint): bigint {
  while (x > 0n) {
    return x;
  }
  return 0n;
}
