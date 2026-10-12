// expected: A3001
function f(): void {
  const xs: number[][] = [[1]];
  const ys = [2];
  xs[0] = ys;
}
