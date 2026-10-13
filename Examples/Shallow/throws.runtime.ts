// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.
export function checked(x: bigint): bigint {
  if (x < 0n) {
    throw new Error("negative");
  }
  return x * 2n;
}

export function relay(x: bigint): bigint {
  return checked(x - 1n);
}

export function firstNegative(xs: readonly bigint[]): bigint {
  let total = 0n;
  for (const x of xs) {
    if (x < 0n) {
      throw new Error("found a negative value");
    }
    total = total + x;
  }
  return total;
}

export function validate(n: bigint): void {
  if (n === 0n) {
    throw new Error("zero");
  }
}

export function always(): bigint {
  throw new Error("unreachable");
}
