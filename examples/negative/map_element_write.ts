// expected: A3001
type Box = { value: number };
function f(xs: Box[]): number[] {
  return xs.map((box: Box) => { box.value = 1; return box.value; });
}
