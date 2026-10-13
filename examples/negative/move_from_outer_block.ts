// expected: A3001
export function f(flag: boolean): bigint[] {
  const a: bigint[] = [];
  if (flag) {
    const b = a;
    b.push(1n);
  }
  return a;
}
