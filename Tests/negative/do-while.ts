// expect: A1001
export function f(n: number): number {
  let i = 0;
  do {
    i++;
  } while (i < n);
  return i;
}
