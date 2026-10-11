export function reverseCodeUnits(text: string): string {
  let result = "";
  let i = text.length;
  while (i > 0) {
    i--;
    result = result + (text[i] ?? "");
  }
  return result;
}

export function palindrome(text: string): boolean {
  return text === reverseCodeUnits(text);
}

export function demo(): string {
  return reverseCodeUnits("A😀\ud800");
}

export function codeUnitLength(): number {
  return "😀".length;
}
