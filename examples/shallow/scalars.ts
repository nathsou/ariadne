export function abs(x: bigint): bigint { if (x < 0n) { return -x; } return x; }
export function update(x: bigint, y: bigint, flag: boolean): bigint { let total = x; if (flag) { total += y; } else { total -= y; } return total * 2n; }
export function fallback(x: bigint | undefined): bigint { return x ?? 9n; }
export function decimal(x: number, y: number): number { return (x * y) / (x + y); }
export function hello(name: string): string { return 'hello ' + name; }
export function optional(flag: boolean, value: bigint): bigint | undefined {
  if (flag) { return value; }
  return undefined;
}
export function textBefore(a: string, b: string): boolean { return a < b; }
export function remainder(a: number, b: number): number { return a % b; }
export function scoped(x: bigint): bigint {
  { let temporary = x + 1n; x = temporary * 2n; }
  let temporary = x - 3n;
  return temporary;
}
export function abs_denotes(): bigint { return 3n; }
export function CoreArtifacts(): bigint { return 4n; }

export function guarded(x: bigint | undefined, floor: bigint): bigint {
  if (x === undefined) { return floor; }
  return x + 1n;
}

export function conjunction(x: bigint | undefined, floor: bigint): boolean {
  return x !== undefined && x > floor;
}

export function disjunction(x: bigint | undefined, floor: bigint): boolean {
  return x === undefined || x >= floor;
}

export function ternary(x: bigint | undefined): bigint {
  return x !== undefined ? x + 1n : 0n;
}

export function forget(x: bigint | undefined, clear: boolean): bigint | undefined {
  if (x !== undefined) {
    if (clear) { x = undefined; } else { x += 1n; }
  }
  return x;
}

export function scopedTypes(x: bigint): bigint {
  { const temporary: string = 'inner'; const unused = temporary + '!'; }
  let temporary: bigint = x;
  if (x > 0n) { temporary += 1n; }
  return temporary;
}
