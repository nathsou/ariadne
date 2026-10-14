// expect: A2002
interface P { x: number }
export function f(ps: readonly P[], p: P): boolean {
  return ps.includes(p);
}
