// Reverses UTF-16 code units, not Unicode code points or grapheme clusters.
export function reverse(text: string): string {
  let result = "";
  for (let i = text.length - 1; i >= 0; i = i - 1) {
    result = result + (text[i] ?? "");
  }
  return result;
}
