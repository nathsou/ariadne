// expect: A1001
export function f(n: number): number {
  let i = 0;
  while (i + 1 < n) {
    i++;
  }
  return i;
}
