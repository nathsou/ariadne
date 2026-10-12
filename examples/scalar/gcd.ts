export function gcd(left: bigint, right: bigint): bigint {
  if (left < 0n) { left = -left; }
  if (right < 0n) { right = -right; }
  while (right !== 0n) {
    const remainder = left % right;
    left = right;
    right = remainder;
  }
  return left;
}
