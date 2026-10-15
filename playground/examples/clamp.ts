// Clamp a number into a range. Ariadne turns this into a Lean definition and a theorem
// saying that every run of the JavaScript returns what the definition computes.

/** `x`, moved into the range from `lo` to `hi`. */
export function clamp(x: number, lo: number, hi: number): number {
  if (x < lo) return lo;
  if (x > hi) return hi;
  return x;
}

/** Whether `x` is already in the range. */
export function inRange(x: number, lo: number, hi: number): boolean {
  return lo <= x && x <= hi;
}
