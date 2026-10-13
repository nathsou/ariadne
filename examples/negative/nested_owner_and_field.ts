// expected: A3001
type Bag = { items: bigint[] };

function both(bag: Bag, items: bigint[]): void {
  bag.items.push(1n);
  items.push(2n);
}

export function f(): Bag {
  const empty: bigint[] = [];
  const bag: Bag = { items: empty.slice() };
  both(bag, bag.items);
  return bag;
}
