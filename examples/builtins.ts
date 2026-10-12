export function searchCallbacks(): string {
  const values: bigint[] = [0n, 1n, 2n];
  const some = values.some((x: bigint) => x === 0n || 1n / (x - 1n) > 0n);
  const every = values.every((x: bigint) => x !== 0n && 1n / (x - 1n) > 0n);
  const found = values.find((x: bigint) => x === 0n || 1n / (x - 1n) > 0n);
  const index = values.findIndex((x: bigint) => x === 0n || 1n / (x - 1n) > 0n);
  const missing = values.find((x: bigint) => x > 2n);
  const empty: bigint[] = [];
  return `${some}|${every}|${found}|${index}|${missing}|${empty.some((x: bigint) => x > 0n)}|${empty.every((x: bigint) => x > 0n)}`;
}

export function stringSearches(): string {
  const text = 'a😀\ud800b';
  return `${text.startsWith('😀', 1)}|${text.endsWith('\ud800', 4)}|${text.includes('\ude00')}|${text.indexOf('b')}|${text.indexOf('', Infinity)}|${text.startsWith('a', -9)}|${text.endsWith('', NaN)}|${text.includes('x')}`;
}

export function arraySearches(): number[] {
  const values: number[] = [NaN, 0, -0, 4];
  return [values.includes(NaN) ? 1 : 0, values.indexOf(NaN), values.indexOf(-0),
    values.indexOf(4, -1), values.indexOf(0, Infinity), values.indexOf(0, -Infinity),
    values.includes(0, -2) ? 1 : 0, values.indexOf(0, 2.9)];
}

export function extrema(): number[] {
  return [Math.min(), Math.max(), Math.min(3, -5, 2), Math.max(3, -5, 2),
    Math.min(0, -0), Math.max(-0, 0), Math.min(NaN, -Infinity), Math.max(Infinity, NaN),
    Math.min(-0, 0), Math.max(0, -0)];
}

type Printable = string | number | bigint | boolean | null | undefined;
export function concatenation(): string {
  const left: number[] = [1, 2];
  const right: number[] = [3, 4];
  const values: Printable[] = ['x', 1e21, 1e-7, -0, 9n, true, null, undefined, NaN, Infinity];
  return left.concat(right, 5).join(':') + '|' + values.join();
}

type Item = { readonly rank: number; readonly id: string };
export function stableSort(): string {
  const values: Item[] = [{ rank: 2, id: 'a' }, { rank: 1, id: 'b' },
    { rank: 2, id: 'c' }, { rank: 1, id: 'd' }];
  const sorted = values.toSorted((a: Item, b: Item) => a.rank - b.rank);
  return sorted.map((item: Item) => item.id).join(',') + '|' +
    values.map((item: Item) => item.id).join(',');
}

type OptionalNumber = number | undefined;
export function sortUndefined(): OptionalNumber[] {
  const values: OptionalNumber[] = [undefined, 3, 1, undefined, 2];
  return values.toSorted((a: OptionalNumber, b: OptionalNumber) => {
    if (a === undefined || b === undefined) { return Number(BigInt(NaN)); }
    return a - b;
  });
}

export function numericTemplates(): string {
  return `${-0}|${NaN}|${Infinity}|${-Infinity}|${0.1}|${1e-6}|${1e-7}|${1e20}|${1e21}|${1000000000000000128}`;
}
