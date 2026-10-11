// expected: A3001
function g(a: number[], b: number[]): void {} function f(): void { const a: number[] = []; g(a, a); }
