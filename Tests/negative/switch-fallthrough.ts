// expect: A1001
type T = { kind: 'a' } | { kind: 'b' };
export function f(t: T): bigint {
  switch (t.kind) {
    case 'a':
      const x = 1n;
    case 'b':
      return 2n;
  }
}
