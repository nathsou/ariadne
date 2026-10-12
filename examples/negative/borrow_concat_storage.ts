// expected: A3001
type Point = { readonly x: bigint }; function f(point: Point): Point[] { const xs: Point[] = []; return xs.concat(point); }
