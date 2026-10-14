// expect: A2002
// A counted loop's bound must be a const (a parameter can be reassigned).
export function f(n: number): number {
  let t = 0;
  for (let i = 0; i < n; i++) {
    t = t + i;
  }
  return t;
}
