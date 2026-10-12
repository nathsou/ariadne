interface Entry { readonly kind: 'entry'; readonly value: bigint; note?: string; }
type Event = { readonly kind: 'add'; readonly value: bigint } | { readonly kind: 'stop' };

export function escapes(): string {
  return 'a\0b\u{1f600}\ud800\x41\v\z';
}

export function templates(): string {
  const name: string = 'world';
  return `hello ${name}: ${`inner ${2n}`} ${true} ${undefined} ${null}`;
}

export function foldEvents(): bigint {
  const events: readonly Event[] = [
    { kind: 'add', value: 2n }, { kind: 'add', value: 5n }, { kind: 'stop' },
  ];
  let result = 0n;
  for (const event of events) {
    switch (event.kind) {
      case 'add':
        result += event.value;
        continue;
      case 'stop':
        return result;
    }
  }
  return result;
}

export function spreads(): bigint {
  const xs = [1n, 2n];
  const ys = [...xs, 3n];
  const record: Entry = { kind: 'entry', value: 4n };
  const copy = { ...record, value: 7n };
  let result = copy.value;
  for (const y of ys) { result += y; }
  return result;
}

class Box {
  private value: bigint = 0n;
  constructor(value: bigint) { this.value = value; }
  add(value: bigint): void { this.value = this.value + value; }
  read(): bigint { return this.value; }
}

export function classes(): bigint {
  const box = new Box(3n);
  box.add(4n);
  return box.read();
}

export function sets(): number[] {
  const values = new Set<number>();
  values.add(NaN);
  values.add(NaN);
  values.add(-0);
  values.add(0);
  values.add(2);
  values.delete(2);
  return [...values.values()];
}

export function nullish(value: bigint | null | undefined): bigint {
  if (value == null) { return 0n; }
  return value;
}

export function narrowing(): bigint {
  return nullish(null) + nullish(undefined) + nullish(7n);
}

export function mapIteration(): bigint {
  const values = new Map<string, bigint>();
  values.set('a', 2n);
  values.set('b', 4n);
  values.set('a', 3n);
  let result = 0n;
  for (const entry of values) { result += entry[1]; }
  return result;
}

export function nestedFresh(): number[] {
  const values = new Map<string, number[]>();
  values.set('a', [1, 2]);
  const xs = values.get('a') ?? [];
  return xs.slice();
}

/** @decreases n */
function measured(n: bigint): bigint {
  let total = 0n;
  /** @decreases n */
  while (n > 0n) { total += n; n -= 1n; }
  return total;
}

export function measures(): bigint { return measured(4n); }
export function conditionalPrecedence(): number[] {
  return [1 + 2 === 3 ? 4 : 5, 1 < 0 ? 6 : 7, !false ? 8 : 9,
    true && false ? 10 : 11, false || true ? 12 : 13,
    false ? 14 : true ? 15 : 16, 2 * 3 > 5 ? 17 + 1 : 19];
}
