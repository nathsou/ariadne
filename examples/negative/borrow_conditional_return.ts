// expected: A3001
function f(xs: readonly bigint[], ys: readonly bigint[], yes: boolean): readonly bigint[] { return yes ? xs : ys; }
