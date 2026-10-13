/** @decreases n */
export function factorial(n: bigint): bigint {
  if (n <= 0n) {
    return 1n;
  }
  return n * factorial(n - 1n);
}

/** @decreases a + b */
export function gcd(a: bigint, b: bigint): bigint {
  if (a <= 0n) {
    return b;
  }
  if (b <= 0n) {
    return a;
  }
  if (a > b) {
    return gcd(a - b, b);
  }
  return gcd(a, b - a);
}

/** @decreases n */
export function fib(n: bigint): bigint {
  if (n < 2n) {
    return n;
  }
  return fib(n - 1n) + fib(n - 2n);
}

export function shifted(n: bigint): bigint {
  return factorial(n) + 1n;
}

// The measure grows here, so the safety condition fails whenever the
// function recurses.
/** @decreases n */
export function wrong(n: bigint): bigint {
  if (n > 100n) {
    return n;
  }
  return wrong(n + 1n);
}
