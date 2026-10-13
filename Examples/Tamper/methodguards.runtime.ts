// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.
export class GuardedBox {
  private count = 0n;
  append(left: bigint[], right: readonly bigint[]): void {
  if (this !== null && typeof this === 'object' && left !== null && typeof left === 'object' && ((this as object) === (left as object))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  if (left !== null && typeof left === 'object' && right !== null && typeof right === 'object' && ((left as object) === (right as object))) {
    throw new TypeError('overlapping borrowed arguments');
  }
  const __ariadne0_implementation = () => { left.push(9n); };
  return __ariadne0_implementation();
}
}
