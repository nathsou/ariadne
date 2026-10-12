// expected: A3002
function f(xs: number[]): number[] {
  let count = 0;
  return xs.toSorted((a: number, b: number) => { count += 1; return a - b; });
}
