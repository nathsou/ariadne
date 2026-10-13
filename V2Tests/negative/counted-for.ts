// expect: A1001
export function f(n: number): number {
  let t = 0;
  for (let i = 0; i < n; i++) {
    t = t + i;
  }
  return t;
}
