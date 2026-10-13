// expected: A3001
function f(a: number[]): void { a[0] += a[1] ?? 0; }
