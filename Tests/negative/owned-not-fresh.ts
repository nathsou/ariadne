// expect: A1001
// `a` is the parameter's array, not a new one.
export function f(xs: number[]): number[] {
  const a = xs;
  a.push(1);
  return a;
}
