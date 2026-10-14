// expect: A1001
export function f(xs: readonly number[]): number[] {
  return xs.map((x, i) => x + i);
}
