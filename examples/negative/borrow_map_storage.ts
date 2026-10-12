// expected: A3001
function f(xs: readonly bigint[]): void { const m = new Map<string, readonly bigint[]>(); m.set("x", xs); }
