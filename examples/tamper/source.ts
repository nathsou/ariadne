// Small source-certificate fixture: primitive/parameter/function checks and
// local declaration, branch condition and assignment-target checks.
export function arithmetic(flag: boolean, x: bigint, y: bigint): bigint {
  return flag ? x + y : x - y;
}

export function flow(x: bigint, y: bigint): bigint {
  const sum = x + y;
  x = x + 1n;
  if (x < y) { return sum; }
  return x;
}
