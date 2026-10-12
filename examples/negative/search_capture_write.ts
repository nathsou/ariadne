// expected: A3002
function f(xs: number[]): boolean {
  let count = 0;
  return xs.some((x: number) => { count += 1; return x > 0; });
}
