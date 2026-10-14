// expect: A2004
function g(): bigint {
  return 1n;
}
export function f(): bigint {
  const g = 2n;
  return g;
}
