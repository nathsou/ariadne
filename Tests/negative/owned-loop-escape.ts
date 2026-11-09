// expect: A1001
// The next iteration changes the array the previous one stored.
export function f(): number[][] {
  const a: number[] = [];
  const out: number[][] = [];
  for (const i of [1, 2]) {
    out.push(a);
    a.push(i);
  }
  return out;
}
