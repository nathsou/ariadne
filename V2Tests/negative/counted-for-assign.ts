// expect: A2002
// A counted loop's index is not assignable in its body.
export function f(n: number): number {
  const m = n;
  let t = 0;
  for (let i = 0; i < m; i++) {
    i = i + 1;
    t = t + i;
  }
  return t;
}
