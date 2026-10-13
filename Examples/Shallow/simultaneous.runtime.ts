// Generated ownership entry wrappers. Requires the Ariadne pristine realm contract.
type Row = { count: bigint };

function swap(left: Row, right: Row): void {
  const saved = left.count;
  left.count = right.count;
  right.count = saved;
}

export function swapRows(rows: Row[], i: number, j: number): void {
  if ((i) === (j)) {
    throw new TypeError('overlapping projected arguments');
  }
  return __ariadne0_swapRows(rows, i, j);
}

function __ariadne0_swapRows(rows: Row[], i: number, j: number): void {
  swap(rows[i], rows[j]);
}

export function swapGroups(groups: Map<string, Row>, a: string, b: string): void {
  if ((a) === (b) || (Number.isNaN(a) && Number.isNaN(b))) {
    throw new TypeError('overlapping projected arguments');
  }
  return __ariadne0_swapGroups(groups, a, b);
}

function __ariadne0_swapGroups(groups: Map<string, Row>, a: string, b: string): void {
  swap(groups.get(a)!, groups.get(b)!);
}

export function swapNumbers(groups: Map<number, Row>, a: number, b: number): void {
  if ((a) === (b) || (Number.isNaN(a) && Number.isNaN(b))) {
    throw new TypeError('overlapping projected arguments');
  }
  return __ariadne0_swapNumbers(groups, a, b);
}

function __ariadne0_swapNumbers(groups: Map<number, Row>, a: number, b: number): void {
  swap(groups.get(a)!, groups.get(b)!);
}

function appendBoth(left: bigint[], right: bigint[]): void {
  left.push(1n);
  right.push(2n);
}

export function appendRows(rows: bigint[][], i: number, j: number): void {
  if ((i) === (j)) {
    throw new TypeError('overlapping projected arguments');
  }
  return __ariadne0_appendRows(rows, i, j);
}

function __ariadne0_appendRows(rows: bigint[][], i: number, j: number): void {
  appendBoth(rows[i], rows[j]);
}
