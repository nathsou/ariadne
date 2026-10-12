// expected: A3001
function f(xs: readonly bigint[]): void { let items: readonly bigint[] = []; items = xs; }
