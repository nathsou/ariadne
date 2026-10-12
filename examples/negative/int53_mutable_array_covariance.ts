// expected: A3001
type Int53 = number;
function appendHalf(xs: number[]): void { xs.push(0.5); }
export function corrupt(xs: Int53[]): void { appendHalf(xs); }
