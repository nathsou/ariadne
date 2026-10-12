// expected: A3001
type Int53 = number;
function addHalf(xs: Set<number>): void { xs.add(0.5); }
export function corrupt(xs: Set<Int53>): void { addHalf(xs); }
