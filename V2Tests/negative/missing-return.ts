// expect: A2003
export function f(x: bigint): bigint {
  if (x > 0n) {
    return x;
  }
}
