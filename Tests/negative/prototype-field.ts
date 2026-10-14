// expect: A2002
interface P { toString: string }
export function f(p: P): string {
  return p.toString;
}
