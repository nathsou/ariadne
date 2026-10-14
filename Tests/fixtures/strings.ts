// Strings and integer division.

export function hasPrefix(s: string, p: string): boolean {
  return s.startsWith(p);
}

export function hasSuffix(s: string, p: string): boolean {
  return s.endsWith(p);
}

export function contains(s: string, t: string): boolean {
  return s.includes(t);
}

export function position(s: string, t: string): number {
  return s.indexOf(t);
}

export function tail(s: string, from: number): string {
  return s.slice(from);
}

export function middle(s: string, from: number, to: number): string {
  return s.slice(from, to);
}

/** The part after the first `sep`, or the whole string. */
export function after(s: string, sep: string): string {
  const i = s.indexOf(sep);
  if (i < 0) return s;
  return s.slice(i + sep.length);
}

export function half(n: number): number {
  return Math.floor(n / 2);
}

export function quotient(a: number, b: number): number {
  return Math.floor(a / b);
}

export function remainder(a: number, b: number): number {
  return a % b;
}

export function bigQuotient(a: bigint, b: bigint): bigint {
  return a / b;
}

export function bigRemainder(a: bigint, b: bigint): bigint {
  return a % b;
}

/** Whether `n` is even, for any safe integer. */
export function even(n: number): boolean {
  return n % 2 === 0;
}

/** The digits of `n`, least significant first. */
export function digits(n: number): number[] {
  let out: number[] = [];
  let m = n < 0 ? -n : n;
  const most = 16;
  for (let i = 0; i < most; i++) {
    out = [...out, m % 10];
    m = Math.floor(m / 10);
    if (m === 0) break;
  }
  return out;
}
