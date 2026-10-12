// A borrowed array is updated in place; it is not returned as an escaping alias.
export function insertionSort(values: number[]): void {
  for (let i = 1; i < values.length; i++) {
    const key = values[i] ?? 0;
    let j = i;
    while (j > 0 && (values[j - 1] ?? 0) > key) {
      values[j] = values[j - 1] ?? 0;
      j--;
    }
    values[j] = key;
  }
}

export function demo(): number[] {
  const values = [9, -2, 7, 7, 0, 3];
  insertionSort(values);
  return values;
}
