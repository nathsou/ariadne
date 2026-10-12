// expected: A2002
function f(xs: number[]): boolean {
  return xs.some((x: number) => { if (x > 0) { return 1; } return false; });
}
