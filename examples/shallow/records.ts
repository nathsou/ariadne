type Point = {
  readonly x: bigint;
  readonly label: string;
  readonly weight?: bigint;
};

type Tagged = { readonly kind: 'ok'; readonly payload: bigint };
type Weird = { readonly length: bigint; readonly size: string; readonly rec: bigint };
type Empty = {};

export function make(x: bigint, label: string): Point {
  return { x: x, label: label, weight: undefined };
}

export function sum(points: readonly Point[]): bigint {
  let total = 0n;
  for (const point of points) { total += point.x + (point.weight ?? 0n); }
  return total;
}

export function find(points: readonly Point[], floor: bigint): Point | undefined {
  return points.find((point: Point) => point.x >= floor);
}

export function relabel(point: Point, label: string): Point {
  return { x: point.x, label: label, weight: point.weight };
}

export function tagged(value: bigint): Tagged { return { kind: 'ok', payload: value }; }
export function tagName(value: Tagged): string { return value.kind; }

export function weird(length: bigint): Weird { return { length: length, size: 'abc', rec: 2n }; }
export function fields(value: Weird): bigint { return value.length + value.rec; }

export function duplicate(): Point { return { x: 1n, x: 2n, label: 'last' }; }
export function empty(): Empty { return {}; }
