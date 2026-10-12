export function transform(xs: readonly bigint[], delta: bigint): bigint[] {
  return xs.filter((x: bigint) => x >= 0n).map((x: bigint) => x * 2n + delta);
}

export function sum(xs: readonly bigint[]): bigint {
  return xs.reduce((acc: bigint, x: bigint) => acc + x, 0n);
}

export function indexed(xs: readonly number[]): number {
  return xs.reduce((acc: number, x: number, i: number) => acc + x * i, 0);
}

export function find(xs: readonly bigint[], floor: bigint): bigint | undefined {
  return xs.find((x: bigint) => x >= floor);
}

export function findIndex(xs: readonly bigint[], floor: bigint): number {
  return xs.findIndex((x: bigint) => x >= floor);
}

export function allPositive(xs: readonly bigint[]): boolean {
  return xs.every((x: bigint) => x > 0n);
}

export function anyPositive(xs: readonly bigint[]): boolean {
  return xs.some((x: bigint) => x > 0n);
}

export function lookup(xs: readonly bigint[], index: number): bigint | undefined {
  return xs[index];
}

export function sliced(xs: readonly bigint[], start: number, stop: number): bigint[] {
  return xs.slice(start, stop).toReversed();
}

export function copy(xs: readonly bigint[]): bigint[] { return xs.slice(); }

export function combined(xs: readonly bigint[]): bigint[] {
  return [1n, ...xs, 2n].concat([3n], 4n);
}

export function constantMap(xs: readonly bigint[]): bigint[] { return xs.map(() => 7n); }

export function count(xs: readonly bigint[]): number { return xs.length; }

export function score(xs: readonly bigint[]): bigint { return sum(xs) + 1n; }

export function empty(): bigint[] { const values: bigint[] = []; return values; }

export function program(Bool: bigint): bigint { return Bool + 1n; }
export function Int(JSArray: readonly bigint[]): bigint[] { return JSArray.map(() => 1n); }
export function afterNames(values: readonly bigint[]): bigint { return sum(values) + program(1n); }
