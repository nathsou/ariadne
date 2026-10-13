// expect: A2004
export function f(xs: readonly number[], x: number): number {
  let t = 0;
  for (const x of xs) {
    t = t + x;
  }
  return t;
}
