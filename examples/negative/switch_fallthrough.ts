// expected: A1001
type Choice = { readonly kind: 'a' } | { readonly kind: 'b'; readonly value: bigint };
function f(choice: Choice): bigint {
  switch (choice.kind) { case 'a': case 'b': return choice.value; }
  return 0n;
}
