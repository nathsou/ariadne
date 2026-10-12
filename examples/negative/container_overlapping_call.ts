// expected: A3001
function merge(a: bigint[], b: bigint[]): void { a.push(1n); b.push(2n); } function f(m: Map<string, bigint[]>): void { merge(m.get("x") ?? [], m.get("x") ?? []); }
