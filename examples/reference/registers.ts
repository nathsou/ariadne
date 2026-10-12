type Int53 = number;

// A stamp identifies an operation: replaying it must use the same value.
// Components of a composite key must not contain NUL.
export class Registers {
  private readonly values = new Map<string, Int53>();
  private readonly stamps = new Map<string, string>();
  private readonly counters = new Map<string, Int53>();

  write(a: string, b: string, value: Int53, stamp: string): void {
    const key = a + '\0' + b;
    const seen = this.stamps.get(key);
    if (seen !== undefined && seen >= stamp) { return; }
    this.values.set(key, value);
    this.stamps.set(key, stamp);
  }

  read(a: string, b: string): Int53 | undefined {
    return this.values.get(a + '\0' + b);
  }

  // Per-replica monotone counter components merge by maximum.
  count(key: string, replica: string, value: Int53): void {
    const component = key + '\0' + replica;
    const seen = this.counters.get(component) ?? 0;
    if (value > seen) { this.counters.set(component, value); }
  }

  counter(key: string, replica: string): Int53 {
    return this.counters.get(key + '\0' + replica) ?? 0;
  }
}
