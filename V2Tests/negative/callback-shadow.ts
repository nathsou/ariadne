// expect: A2004
export function f(xs: readonly number[], x: number): boolean {
  return xs.some((x) => x > 0);
}
