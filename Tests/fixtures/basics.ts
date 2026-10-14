export function max(a: bigint, b: bigint): bigint {
  if (a < b) {
    return b;
  }
  return a;
}

export function clamp(x: bigint, lo: bigint, hi: bigint): bigint {
  const y = max(x, lo);
  return y > hi ? hi : y;
}

function sign(n: bigint): bigint {
  if (n < 0n) {
    return -1n;
  } else if (n === 0n) {
    return 0n;
  }
  return 1n;
}

export function describe(n: bigint, label: string): string {
  const s = sign(n);
  const prefix = label + ": ";
  if (s === 0n) {
    return prefix + "zero";
  }
  const kind = s > 0n ? "positive" : "negative";
  if (label === "" || label <= "a") {
    return kind;
  }
  return prefix + kind;
}

export function between(lo: string, x: string, hi: string): boolean {
  return !(x < lo) && x <= hi && lo !== hi;
}

export function polynomial(x: bigint): bigint {
  const square = x * x;
  const cube = square * x;
  return cube - 2n * square + 3n * x - 4n;
}

export function implies(a: boolean, b: boolean): boolean {
  if (a) {
    const t = b === true;
    if (t) {
      return true;
    }
    return false;
  }
  return true;
}
