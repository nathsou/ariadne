// expected: A3001
function f(a: Map<string, number>): Map<string, number> { return a.set("x", 1); }
