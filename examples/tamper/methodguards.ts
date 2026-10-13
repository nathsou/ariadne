export class GuardedBox {
  private count = 0n;
  append(left: bigint[], right: readonly bigint[]): void { left.push(9n); }
}
