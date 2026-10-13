export function gcd(a: bigint, b: bigint): bigint {
  let x = a < 0n ? -a : a;
  let y = b < 0n ? -b : b;
  /** @decreases x + y */
  while (x > 0n && y > 0n) {
    if (x > y) {
      x = x - y;
    } else {
      y = y - x;
    }
  }
  return x + y;
}

export function countdown(n: bigint): bigint {
  let i = n;
  let steps = 0n;
  /** @decreases i */
  while (i > 0n) {
    i = i - 1n;
    steps = steps + 1n;
  }
  return steps;
}

export function doubling(limit: bigint): bigint {
  let p = 1n;
  /** @decreases limit - p */
  while (p < limit) {
    if (p > 1000n) {
      break;
    }
    p = p * 2n;
  }
  return p;
}

export function root(limit: bigint, target: bigint): bigint {
  let i = 0n;
  /** @decreases limit - i */
  while (i < limit) {
    if (i * i === target) {
      return i;
    }
    i = i + 1n;
  }
  return -1n;
}

// The measure grows here, so the loop's safety condition fails whenever the
// loop runs: the denotation is still total, but no adequacy claim follows.
export function climb(n: bigint): bigint {
  let i = n;
  /** @decreases i */
  while (i < 10n) {
    i = i + 1n;
  }
  return i;
}
