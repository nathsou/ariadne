// Keys are UTF-16 code units, matching TypeScript's indexed string access.
export function histogram(text: string): Map<string, number> {
  const counts = new Map<string, number>();
  for (let i = 0; i < text.length; i++) {
    const key = text[i] ?? "";
    counts.set(key, (counts.get(key) ?? 0) + 1);
  }
  return counts;
}

export function demo(): Map<string, number> {
  return histogram("abracadabra");
}
