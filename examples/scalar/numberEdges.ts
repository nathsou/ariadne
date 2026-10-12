// Includes NaN, infinities, and signed zero; arithmetic stays binary64.
export function numberEdges(left: number, right: number): number {
  const remainder = left % right;
  if (remainder === 0) { return -remainder; }
  return remainder;
}
