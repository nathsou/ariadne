// expect: A2002
interface P { x: bigint }
export function f(p: P, q: P): boolean {
  return p === q;
}
