// expected: A3004
class Counter { private value = 0n; read(): bigint { return this.value; } }
function demo(Counter: bigint): bigint { const value = new Counter(); return value.read(); }
