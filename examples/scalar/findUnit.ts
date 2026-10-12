// The caller can pass a single UTF-16 code unit, including a lone surrogate.
export function findUnit(text: string, unit: string): number {
  for (let i = 0; i < text.length; i = i + 1) {
    if (text[i] === unit) { return i; }
  }
  return -1;
}
