// expect: A2003
export function f(x: number): number {
  if (x > 0) continue;
  return x;
}
