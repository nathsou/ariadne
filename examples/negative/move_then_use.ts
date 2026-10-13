// expected: A3001
export function f(): bigint[] {
  const a: bigint[] = [];
  const b = a;
  b.push(1n);
  a.push(2n);
  return b;
}
