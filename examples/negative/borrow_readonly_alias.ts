// expected: A3001
function f(xs: readonly bigint[]): bigint { const alias = xs; return alias.length === 0 ? 0n : 1n; }
