// expect: A1001
function big(x: number): boolean {
  return x > 2;
}
export function f(xs: readonly number[]): number[] {
  return xs.filter(big);
}
