// expect: A1001
// Arrays are values in the model: in-place mutation is refused.
export function f(xs: number[]): number[] {
  xs.push(1);
  return xs;
}
