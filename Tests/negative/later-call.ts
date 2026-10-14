// expect: A2001
export function f(): bigint {
  return g();
}
function g(): bigint {
  return 1n;
}
