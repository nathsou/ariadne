export function choose(enabled: boolean, text: string | undefined): string {
  if (enabled) { return text ?? "fallback"; }
  return "";
}
