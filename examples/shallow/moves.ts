export function build(n: bigint): bigint[] {
  const items: bigint[] = [];
  items.push(n);
  const result = items;
  result.push(n + 1n);
  return result;
}

export function handoff(xs: readonly bigint[]): bigint {
  const copy = xs.slice();
  const owned = copy;
  owned.push(10n);
  return owned.reduce((acc: bigint, x: bigint) => acc + x, 0n);
}

export function chain(n: bigint): bigint[] {
  const first: bigint[] = [n];
  const second = first;
  const third = second;
  third.push(n * 2n);
  return third;
}

export function scoped(flag: boolean): bigint[] {
  const out: bigint[] = [];
  if (flag) {
    const inner: bigint[] = [1n];
    const moved = inner;
    moved.push(2n);
    out.push(moved.length === 2 ? 1n : 0n);
  }
  return out;
}
