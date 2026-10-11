export function lookupOrDefault(key: string, fallback: bigint): bigint {
  const entries = new Map<string, bigint>();
  entries.set("answer", 42n);
  return entries.get(key) ?? fallback;
}

export function demo(): bigint {
  return lookupOrDefault("missing", 7n);
}

export function negativeDivision(): bigint {
  return -17n / 5n;
}

export function negativeRemainder(): bigint {
  return -17n % 5n;
}
