// expect: A1001
type P = { x: number };
export function f(p: P): P {
  p.x = 1;
  return p;
}
