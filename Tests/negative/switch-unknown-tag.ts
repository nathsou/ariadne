// expect: A2002
type T = { kind: 'a' } | { kind: 'b' };
export function f(t: T): bigint {
  switch (t.kind) {
    case 'a':
      return 1n;
    case 'c':
      return 2n;
  }
  return 0n;
}
