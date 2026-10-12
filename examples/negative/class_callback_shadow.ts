// expected: A3004
class Counter { private value = 0n; read(): bigint { return this.value; } }
function demo(values: readonly bigint[]): bigint[] {
  return values.map((Counter: bigint) => { const value = new Counter(); return value.read(); });
}
