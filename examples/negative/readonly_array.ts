// expected: A3001
function f(xs: readonly bigint[]): void { xs.push(2n); }
