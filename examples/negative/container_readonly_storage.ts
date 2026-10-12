// expected: A3001
function f(m: Map<string, bigint[]>): void { const rows: (readonly bigint[])[] = []; rows.push(m.get("x") ?? [1n]); }
