// expect: A1001
// Pushing an array into itself makes it refer to itself.
export function f(): number[][] {
  const a: number[][] = [];
  a.push(a);
  return a;
}
