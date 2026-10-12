type Int53 = number;
type Size = Int53;

export function add(a: Int53, b: Int53): Int53 { return a + b; }
export function multiply(a: Int53, b: Int53): Int53 { return a * b; }
export function negate(a: Int53): Int53 { return -a; }
export function remainder(a: Int53, b: Int53): Int53 { return a % b; }
export function floorDivide(a: Int53, b: Int53): Int53 { return Math.floor(a / b); }
export function truncDivide(a: Int53, b: Int53): Int53 { return Math.trunc(a / b); }
export function absolute(a: Int53): Int53 { return Math.abs(a); }
export function minimum(a: Int53, b: Int53, c: Int53): Int53 { return Math.min(a, b, c); }
export function maximum(a: Int53, b: Int53): Int53 { return Math.max(a, b); }
export function widen(a: Int53): number { return a + 0.5; }
export function count(xs: readonly Int53[]): Size { return xs.length; }
export function chooseBranch(a: Int53, increment: boolean): Int53 {
  if (increment) { return a + 1; }
  return a;
}
export function total(xs: readonly Int53[]): Int53 {
  return xs.reduce((sum: Int53, value: Int53) => sum + value, 0);
}
export function firstZero(xs: readonly Int53[]): boolean {
  return xs.some((value: Int53) => {
    if (value === 0) { return true; }
    return value + 1 === 0;
  });
}
export function through(n: Int53, stop: Int53): Int53 {
  let sum = 0;
  for (let i = 0; i < n; i++) {
    if (i === stop) { break; }
    sum += i;
  }
  return sum;
}
export function optionalEqual(a: Int53 | undefined, b: Int53): boolean { return a === b; }
export function optionalPair(a: Int53 | undefined, b: Int53 | undefined): boolean { return a === b; }
