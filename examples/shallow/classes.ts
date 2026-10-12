export class Counter {
  private value = 0n;
  private readonly counts = new Map<string, bigint>();
  read(): bigint { return this.value; }
  add(amount: bigint): void { this.value = this.value + amount; }
  bump(key: string): bigint {
    const next = (this.counts.get(key) ?? 0n) + 1n;
    this.counts.set(key, next);
    return next;
  }
  count(key: string): bigint { return this.counts.get(key) ?? 0n; }
  twice(amount: bigint): bigint {
    this.add(amount);
    this.add(amount);
    return this.read();
  }
  until(keys: readonly string[], stop: string): void {
    for (const key of keys) {
      if (key === stop) { return; }
      this.bump(key);
    }
  }
}
export class Seeded {
  private value = 0n;
  constructor(initial: bigint) { this.value = initial; }
  add(amount: bigint): void { this.value = this.value + amount; }
  read(): bigint { return this.value; }
}
export function useCounter(key: string): bigint {
  const counter = new Counter();
  counter.add(3n);
  counter.bump(key);
  counter.twice(2n);
  return counter.read() + counter.count(key);
}
export function useSeeded(value: bigint): bigint {
  const counter = new Seeded(value);
  counter.add(2n);
  return counter.read();
}
export function bumpBorrowed(counter: Counter, key: string): bigint {
  return counter.bump(key);
}
export function addBorrowed(counter: Seeded, amount: bigint): void {
  counter.add(amount);
}
