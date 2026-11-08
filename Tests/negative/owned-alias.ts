// expect: A1001
// Once another array holds it, `a` is not changed in place: `b[0]` would see the change.
export function f(): number[] {
  const a: number[] = [];
  const b: number[][] = [a];
  a.push(1);
  return b[0] ?? [];
}
