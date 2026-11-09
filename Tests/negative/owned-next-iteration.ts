// expect: A1001
// `g` keeps the array an iteration pushed it, which the next iteration changes.
export function f(): number[][] {
  const a: number[] = [];
  const g: number[][] = [];
  for (const x of [1, 2]) {
    a.push(x);
    g.push(a);
  }
  return [a, ...g];
}
