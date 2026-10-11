// Euclid's algorithm exercises remainder, loops, and sequential local mutation.
export function gcd(a: bigint, b: bigint): bigint {
  while (b !== 0n) {
    const remainder = a % b;
    a = b;
    b = remainder;
  }
  return a;
}

export function lcm(a: bigint, b: bigint): bigint {
  if (a === 0n || b === 0n) { return 0n; }
  return (a / gcd(a, b)) * b;
}

export function demo(): bigint {
  return lcm(84n, 30n);
}
