// Binary search, and the bug that hid in Java's for nine years: `(lo + hi) / 2` overflows when
// both ends are large. In JavaScript, numbers past 2^53 lose precision instead of wrapping, which
// is just as wrong. Ariadne's model treats any result outside the safe integers as leaving the
// model, so each function gets a safety condition saying when that cannot happen.

/** The midpoint, as the textbook writes it. Its safety condition requires `lo + hi` to be a
 * safe integer. */
export function midpointNaive(lo: number, hi: number): number {
  return Math.floor((lo + hi) / 2);
}

/** The midpoint, computed from the distance. Safe whenever `0 <= lo <= hi`. */
export function midpoint(lo: number, hi: number): number {
  return lo + Math.floor((hi - lo) / 2);
}

/** The index of `target` in the sorted array `xs`, or -1 when it is absent. */
export function indexOf(xs: readonly number[], target: number): number {
  let lo = 0;
  let hi = xs.length;
  while (lo < hi) {
    const mid = midpoint(lo, hi);
    const v = xs[mid];
    if (v == null) return -1;
    if (v === target) return mid;
    if (v < target) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  return -1;
}
