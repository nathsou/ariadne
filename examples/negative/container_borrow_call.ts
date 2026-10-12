// expected: A3001
function append(xs: bigint[]): void { xs.push(1n); } function f(m: Map<string, bigint[]>): void { append(m.get("x") ?? []); }
