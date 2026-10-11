// expected: A3001
function f(flag: boolean, a: number[], b: number[]): void {
  const alias = flag ? a : b;
}
