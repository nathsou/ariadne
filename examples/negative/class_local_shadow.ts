// expected: A3004
class Counter { private value = 0n; read(): bigint { return this.value; } }
function demo(): bigint { const Counter = 1n; const value = new Counter(); return value.read(); }
