// expect: A1001
type T = { kind: 'a' } | { kind: 'b' };
export function f(t: T): bigint {
  switch (t.kind) {
    case 'b':
      return 2n;
    case 'a':
      return 1n;
  }
}
