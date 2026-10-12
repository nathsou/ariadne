// expected: A3001
function f(xs: readonly bigint[]): void { const rows: (readonly bigint[])[] = []; rows.push(xs); }
