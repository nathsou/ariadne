// expect: A1001
// A loop variable is an element of another array.
interface R {
  n: number;
}
export function f(rs: R[]): number {
  for (const r of rs) {
    r.n = 1;
  }
  return 0;
}
