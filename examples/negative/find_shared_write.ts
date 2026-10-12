// expected: A3001
type Box = { value: number };
function f(xs: Box[]): void {
  const found = xs.find((box: Box) => box.value > 0);
  if (found !== undefined) { found.value = 2; }
}
