const ROOT = 'root';
export const LIMIT = 1679615;
const NEXT: number = LIMIT - 1;

export function isRoot(id: string): boolean {
  return id === ROOT;
}

export function clamp(n: number): number {
  return Math.min(Math.max(n, 0), NEXT);
}
