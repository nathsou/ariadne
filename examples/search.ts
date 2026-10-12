// Missing reads are explicit, even though the loop invariant implies valid bounds.
export function binarySearch(values: number[], target: number): number {
  let low = 0;
  let high = values.length;
  while (low < high) {
    const middle = Math.floor((low + high) / 2);
    const value = values[middle] ?? 0;
    if (value < target) { low = middle + 1; } else { high = middle; }
  }
  if (low < values.length && (values[low] ?? 0) === target) { return low; }
  return -1;
}

export function demo(): number {
  const values = [-8, -3, 0, 4, 7, 12, 19, 31];
  return binarySearch(values, 12);
}
