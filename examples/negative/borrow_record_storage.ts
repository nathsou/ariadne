// expected: A3001
function f(xs: readonly bigint[]): void { const holder = { items: xs }; }
