// expect: A1001
// A loop over an array sees what its body pushes.
export function f(): number[] {
  const a: number[] = [1];
  for (const x of a) {
    a.push(x);
  }
  return a;
}
