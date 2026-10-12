// expected: A3001
type Data =
  | { readonly kind: 'a'; readonly values: readonly bigint[] }
  | { readonly kind: 'b'; readonly values: readonly bigint[] };
function mutate(data: Data): void { data.values.push(1n); }
