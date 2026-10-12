// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.
export function arithmetic(x: bigint, y: bigint): bigint { return -(x + y) * (x - y); }
export function quotient(x: number, y: number): number { return (x * y) / (x + y); }
export function choice(flag: boolean, x: bigint, y: bigint): bigint { return flag ? x : y; }
// This user name must not collide with the generated source theorem for choice.
export function choice_source(): bigint { return 7n; }
export function conjunction(a: boolean, b: boolean): boolean { return a && !b; }
export function disjunction(a: boolean, b: boolean): boolean { return a || !b; }
export function compare(x: bigint, y: bigint): boolean { return x <= y; }
export function equal(x: string, y: string): boolean { return x === y; }
export function text(name: string): string { return 'hello ' + name; }
export function unit(): void { return; }

export function local(a: bigint, b: bigint): bigint {
  const sum = a + b;
  const doubled = sum * 2n;
  return doubled;
}

export function early(value: bigint): bigint {
  if (value < 0n) { return -value; }
  return value;
}

export function branchLocal(flag: boolean, a: bigint, b: bigint): bigint {
  if (flag) {
    const sum = a + b;
    return sum;
  }
  const difference = a - b;
  return difference;
}

export function nested(flag: boolean, other: boolean, value: bigint): bigint {
  if (flag) {
    if (other) { return value; }
    return -value;
  }
  return 0n;
}

export function reassign(value: bigint, delta: bigint): bigint {
  value = value + delta;
  value = value * 2n;
  return value;
}

export function preserveOther(value: bigint): bigint {
  const saved = value;
  value = value + 1n;
  return saved + value;
}

export function branchAssign(value: bigint): bigint {
  if (value < 0n) {
    value = -value;
    return value;
  }
  return value;
}

export function reassignString(value: string, suffix: string): string {
  value = value + suffix;
  return value;
}
