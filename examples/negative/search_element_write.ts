// expected: A3001
type Box = { value: number };
function f(xs: Box[]): boolean {
  return xs.some((box: Box) => { box.value = 1; return true; });
}
