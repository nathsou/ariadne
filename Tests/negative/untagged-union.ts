// expect: A1001
type T = { a: bigint } | { b: string };
export function f(t: T): bigint {
  return 0n;
}
