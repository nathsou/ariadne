type Int53 = number;
type Maybe = Int53 | undefined;
type Nested = Maybe | undefined;
type OptionalRecord = { value?: Maybe };
export function missing(xs: readonly Maybe[]): boolean { return xs[0] === undefined; }
export function present(xs: readonly Maybe[]): boolean { return xs[0] !== undefined; }
export function fallback(xs: readonly Maybe[], defaultValue: Int53): Int53 { return xs[0] ?? defaultValue; }
export function foundMissing(xs: readonly Maybe[]): boolean { return xs.find((x: Maybe) => true) === undefined; }
export function mapMissing(values: ReadonlyMap<bigint, Maybe>, key: bigint): boolean { return values.get(key) === undefined; }
export function mapFallback(values: ReadonlyMap<bigint, Maybe>, key: bigint, defaultValue: Int53): Int53 { return values.get(key) ?? defaultValue; }
export function unitMissing(xs: readonly undefined[]): boolean { return xs[0] === undefined; }
export function nestedMissing(value: Nested): boolean { return value === undefined; }
export function recordMissing(value: OptionalRecord): boolean { return value.value === undefined; }
function checkedUndefined(x: Int53): undefined { const next: Int53 = x + 1; return undefined; }
export function retainedCoercion(x: Int53): Maybe { return checkedUndefined(x); }
export function retainedLeft(x: Int53, value: Maybe): boolean { return checkedUndefined(x) === value; }
export function retainedRight(value: Maybe, x: Int53): boolean { return value === checkedUndefined(x); }
export function retainedUnits(x: Int53): boolean { return checkedUndefined(x) === undefined; }
type LiteralContainer = { readonly xs: readonly "ok"[] };
type OptionalTag = { readonly kind?: "ok" };
type UndefinedRecord = { readonly value?: undefined };
export function literalPresent(value: LiteralContainer): boolean { return value.xs[0] !== undefined; }
export function tagPresent(value: OptionalTag): boolean { return value.kind !== undefined; }
export function unitField(value: UndefinedRecord): boolean { return value.value === undefined; }
