// expected: A3001
type Box = { readonly items: readonly bigint[] }; function f(box: Box): readonly bigint[] { return box.items; }
