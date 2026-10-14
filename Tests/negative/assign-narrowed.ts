// expect: A2002
export function f(x: number | undefined): number {
  if (x == null) return 0;
  x = undefined;
  return 1;
}
