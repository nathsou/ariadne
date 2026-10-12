// expected: A3004
function helper(): bigint { return 1n; }
class Counter {
  private value = 0n;
  constructor(helper: bigint) { this.value = helper(); }
}
