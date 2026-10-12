// expected: A3001
function f(xs: Map<string, number[]>): void { (xs.get('a') ?? []).push(1); }
