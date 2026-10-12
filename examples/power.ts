// Exponentiation by squaring uses logarithmically many loop iterations.
export function power(base: bigint, exponent: bigint): bigint {
  let result = 1n;
  while (exponent > 0n) {
    if (exponent % 2n === 1n) { result *= base; }
    base *= base;
    exponent /= 2n;
  }
  return result;
}

export function demo(): bigint {
  return power(3n, 25n);
}
