export function rounding(): boolean {
  return 0.1 + 0.2 !== 0.3;
}

export function negativeZero(): number {
  return 1 / -0;
}

export function remainder(): number {
  return -5.5 % 2;
}

export function demo(): number {
  return Math.sqrt(144) + Math.floor(-2.5);
}

export function integerPrecisionLimit(): boolean {
  return 9007199254740992 + 1 === 9007199254740992;
}

export function underflow(): number {
  return 1e-324;
}

export function negativeUnderflow(): number {
  return -1e-324;
}

export function overflow(): number {
  return 1e308 * 1e308;
}

export function nanIsUnordered(): boolean {
  return NaN < 1 || NaN === NaN;
}

export function negativeZeroRemainder(): number {
  return -4 % 2;
}

export function truncNegativeZero(): number {
  return 1 / Math.trunc(-0);
}

export function sqrtNegative(): number {
  return Math.sqrt(-1);
}

export function infinityRemainder(): number {
  return 1 % Infinity;
}
