export function nested(flag: boolean, x: bigint): bigint {
  if (flag) { { const y = x + 1n; x = y * 2n; } }
  else { x -= 1n; }
  return x * 3n;
}

export function greater(x: bigint, y: bigint): boolean { return x > y; }
