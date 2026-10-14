// expect: A1001
// Maps are supported only as class fields.
export function f(k: string): boolean {
  const m: Map<string, number> = new Map<string, number>();
  return m.has(k);
}
