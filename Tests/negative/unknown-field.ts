// expect: A2002
interface P { x: bigint }
export function f(p: P): bigint {
  return p.y;
}
