// expect: A1001
// A parameter is the caller's array: changing it in place is refused (only owned locals change in place).
export function f(xs: number[]): number[] {
  xs.push(1);
  return xs;
}
