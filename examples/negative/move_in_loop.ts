// expected: A3001
export function f(xs: readonly bigint[]): bigint[] {
  const a: bigint[] = [];
  for (const x of xs) {
    const b = a;
    b.push(x);
  }
  return a;
}
