// Text resembling the old emitter's sentinels is ordinary source data.
export function marker(): string {
  return "⟦⟦99⟧⟧ne.«fake».«binding»⟦⟦/⟧⟧";
}

// Nested declarations must precede the loop that calls them. Capture only values
// available in the enclosing scope, including a variable used by the inner loop.
export function nested(xs: bigint[], ys: bigint[], offset: bigint): bigint {
  let total = 0n;
  for (const x of xs) {
    for (const y of ys) {
      total = total + x + y + offset;
    }
  }
  return total;
}

export function midpoint(lo: number, hi: number): number {
  return Math.floor((lo + hi) / 2);
}
