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
