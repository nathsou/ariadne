export function demo(): number {
  let total = 0;
  for (let i = 0; i < 20; i++) {
    if (i === 12) { break; }
    if (i % 2 === 0) { continue; }
    total += i;
  }
  return total;
}

export function earlyReturn(limit: bigint): bigint {
  let i = 0n;
  while (i < limit) {
    if (i * i > limit) { return i; }
    i += 1n;
  }
  return limit;
}

export function diverges(): void {
  while (true) { }
}
