// expect: A1001
export function f(xs: number[]): number[] {
  xs[0] = 1;
  return xs;
}
