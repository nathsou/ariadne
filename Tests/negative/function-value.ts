// expect: A2002
function both(x: number, y: number): boolean {
  return x > y;
}
export function f(xs: readonly number[]): number[] {
  return xs.filter(both);
}
