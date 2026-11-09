// expect: A1001
// A constant's value is a literal or arithmetic on earlier constants.
function g(): number {
  return 1;
}
const C: number = g();
export function f(): number {
  return C;
}
