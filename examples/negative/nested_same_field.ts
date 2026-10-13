// expected: A3001
type Bag = { items: bigint[] };

function pair(a: bigint[], b: bigint[]): void {
  a.push(1n);
  b.push(2n);
}

export function f(): Bag {
  const empty: bigint[] = [];
  const bag: Bag = { items: empty.slice() };
  pair(bag.items, bag.items);
  return bag;
}
