export function demo(): Map<number, string> {
  const entries = new Map<number, string>();
  entries.set(NaN, "first");
  entries.set(NaN, "replacement");
  entries.set(-0, "zero");
  entries.set(2, "two");
  entries.delete(0);
  entries.set(0, "reinserted");
  return entries;
}

export function countedValues(): bigint {
  const entries = new Map<string, bigint>();
  entries.set("a", 2n);
  entries.set("b", 5n);
  let total = 0n;
  entries.forEach((value: bigint, key: string) => { total += value; });
  return total;
}

export function presentUndefined(): boolean[] {
  const entries = new Map<string, undefined>();
  entries.set("present", undefined);
  return [entries.has("present"), entries.has("missing"),
    entries.get("present") === entries.get("missing")];
}
