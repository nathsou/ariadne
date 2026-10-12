// expected: A3001
function f(m: Map<string, bigint[]>): readonly bigint[] { return m.get("x") ?? [1n]; }
