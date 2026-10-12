// Exact arithmetic and branching over arbitrary-size integers.
export function absolute(x: bigint): bigint {
  if (x < 0n) { return -x; } else { return x; }
}

export function maximum(x: bigint, y: bigint): bigint {
  if (x < y) { return y; } else { return x; }
}

export function clamp(x: bigint, low: bigint, high: bigint): bigint {
  if (x < low) { return low; }
  if (x > high) { return high; }
  return x;
}

export function demo(): bigint {
  return absolute(-123456789012345678901234567890n);
}
