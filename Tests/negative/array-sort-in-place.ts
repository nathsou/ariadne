// expect: A1001
// `sort` mutates its receiver; `toSorted` is the supported form.
export function f(xs: number[]): number[] {
  return xs.sort((a, b) => a - b);
}
