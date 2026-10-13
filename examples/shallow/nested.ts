type Bag = { items: bigint[]; extra: bigint[]; label: string };

function addTwice(xs: bigint[], x: bigint): void {
  xs.push(x);
  xs.push(x);
}

function appendAll(target: bigint[], source: readonly bigint[]): bigint {
  let count = 0n;
  for (const x of source) {
    target.push(x);
    count = count + 1n;
  }
  return count;
}

function split(small: bigint[], large: bigint[], source: readonly bigint[]): void {
  for (const x of source) {
    if (x < 10n) {
      small.push(x);
    } else {
      large.push(x);
    }
  }
}

function fresh(label: string): Bag {
  const empty: bigint[] = [];
  return { items: empty.slice(), extra: empty.slice(), label: label };
}

export function fill(n: bigint): Bag {
  const bag = fresh("fill");
  addTwice(bag.items, n);
  return bag;
}

export function both(n: bigint): Bag {
  const bag = fresh("both");
  addTwice(bag.items, n);
  addTwice(bag.extra, n + 1n);
  return bag;
}

export function counted(xs: readonly bigint[]): bigint {
  const bag = fresh("counted");
  const added = appendAll(bag.items, xs);
  const more = appendAll(bag.extra, xs);
  return added + more;
}

export function partition(xs: readonly bigint[]): Bag {
  const bag = fresh("partition");
  split(bag.items, bag.extra, xs);
  return bag;
}
