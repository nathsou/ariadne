// expect: A1001
export function f(x: number): number {
  const Math = { floor: (y: number) => y + 1 };
  return Math.floor(x / 2);
}
