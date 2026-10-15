// Named types as Lean declarations: interfaces as variants, anonymous unions, unions and records
// that keep a tuple or sum because their names cannot be a structure's or an inductive's.
export interface Circle { kind: 'circle'; r: number }
export interface Rect { kind: 'rect'; w: number; h: number }
export type Shape = Circle | Rect | { kind: 'dot' };
export type Figure = Shape;

export interface Weird { rec: number; mk: string }
export type Odd = { k: 'rec'; n: number } | { k: 'mk' };

export interface Scene { name: string; shapes: Shape[]; focus?: Shape }

export function area(s: Shape): number {
  switch (s.kind) {
    case 'circle':
      return 3 * s.r * s.r;
    case 'rect':
      return s.w * s.h;
    case 'dot':
      return 0;
  }
}

export function widen(s: Shape, d: number): Shape {
  switch (s.kind) {
    case 'circle': {
      const bigger: Circle = { ...s, r: s.r + d };
      return bigger;
    }
    case 'rect': {
      const wider: Rect = { ...s, w: s.w + d };
      return wider;
    }
    default:
      return s;
  }
}

export function unit(n: number): Figure {
  if (n > 0) return { kind: 'rect', w: n, h: n };
  if (n < 0) return { kind: 'circle', r: -n };
  return { kind: 'dot' };
}

export function circleOf(c: Circle): number {
  return c.r;
}

export function side(s: Rect | { kind: 'pt'; at: number } | { kind: 'none' }): number {
  switch (s.kind) {
    case 'rect': {
      const t = s.w + s.h;
      return t;
    }
    case 'pt':
      return s.at;
    default:
      return -1;
  }
}

export function pair(p: { tag: 'two'; a: number; b: string } | { tag: 'zero' }): string {
  switch (p.tag) {
    case 'two':
      return p.b + '!';
    case 'zero':
      return '';
  }
}

export function weird(w: Weird): Weird {
  return { ...w, rec: w.rec + 1 };
}

export function oddValue(o: Odd): number {
  switch (o.k) {
    case 'rec':
      return o.n;
    case 'mk':
      return 0;
  }
}

export function total(sc: Scene): number {
  let t = 0;
  for (const s of sc.shapes) {
    t = t + area(s);
  }
  const f = sc.focus;
  if (f != null) t = t + area(f);
  return t;
}

export function grow(sc: Scene, d: number): Scene {
  return { ...sc, shapes: sc.shapes.map((s) => widen(s, d)) };
}
