type Point = { readonly x: bigint; readonly label: string; readonly weight?: bigint };

export function relabel(point: Point, label: string): Point {
  return { x: point.x, label: label, weight: point.weight };
}

export function shift(point: Point, delta: bigint): bigint {
  return point.x + delta;
}
