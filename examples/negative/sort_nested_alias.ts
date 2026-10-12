// expected: A3001
type Box = { value: number };
function f(xs: Box[]): Box[] {
  return xs.toSorted((a: Box, b: Box) => a.value - b.value);
}
