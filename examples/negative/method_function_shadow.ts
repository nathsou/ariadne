// expected: A3004
function helper(): bigint { return 1n; }
class Counter {
  read(helper: bigint): bigint { return helper(); }
}
