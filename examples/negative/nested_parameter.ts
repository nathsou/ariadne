// expected: A3001
function f(a: number[][]): void { const inner = a[0] ?? []; inner.push(1); }
