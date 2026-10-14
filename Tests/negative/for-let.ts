// expect: A1001
export function f(xs: readonly number[]): number {
  let t = 0;
  for (let x of xs) {
    t = t + x;
  }
  return t;
}
