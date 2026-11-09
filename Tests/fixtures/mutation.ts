interface Item {
  id: string;
  n: number;
}

function byId(a: Item, b: Item): number {
  return a.id < b.id ? -1 : b.id < a.id ? 1 : 0;
}

export function evens(xs: number[]): number[] {
  const out: number[] = [];
  for (const x of xs) {
    if (x % 2 === 0) out.push(x);
  }
  return out;
}

export function sortedItems(items: Item[]): Item[] {
  const all: Item[] = [...items];
  all.sort(byId);
  return all;
}

export function bump(item: Item): Item {
  const copy = { ...item };
  copy.n = copy.n + 1;
  return copy;
}

export function distinct(xs: string[]): string[] {
  const seen = new Map<string, boolean>();
  const out: string[] = [];
  for (const x of xs) {
    if (seen.has(x)) continue;
    seen.set(x, true);
    out.push(x);
  }
  seen.delete('');
  return [...seen.keys()];
}

export function dropLast(xs: number[]): number[] {
  const ys = [...xs];
  ys.push(1);
  return ys.slice(0, -1);
}

export function stackSum(xs: number[]): number {
  const stack: number[] = [...xs];
  let total = 0;
  while (stack.length > 0) {
    const top = stack[stack.length - 1] ?? 0;
    stack.pop();
    if (top > 0 && top < 1000) total = total + top;
  }
  return total;
}

export function countDistinct(xs: string[]): number {
  const seen = new Map<string, boolean>();
  for (const x of xs) seen.set(x, true);
  return seen.size;
}
