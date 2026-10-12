// expected: A3001
interface Item { readonly value: bigint; }
function f(item: Item): void { item.value = 2n; }
