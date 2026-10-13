// expect: A2002
export function f(x: number): number {
  const y = x;
  y = y + 1;
  return y;
}
