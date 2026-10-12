// expected: A3001
function f(m: Map<string, bigint[]>): void { const xs = m.get("x") ?? []; xs.push(1n); }
