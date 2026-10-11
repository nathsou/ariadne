// expected: A3003
function g(x: number): number { return x; } function f(): number[] { const a = [1]; return a.map((x: number) => g(x)); }
