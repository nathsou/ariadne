// expected: A3001
class Box { constructor(xs: bigint[]) { xs.push(1n); } } function f(m: Map<string, bigint[]>): Box { return new Box(m.get("x") ?? []); }
