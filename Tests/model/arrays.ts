// Model validation: integer numbers, arrays, callbacks, sorting.
interface Item { id: number; rank: number; name: string }

export function t_numbers(): number[] {
  const a = 9007199254740990;
  return [a + 1, -a - 1, 3 * 4 - 5, 0 * -1, 2 - 3];
}

export function fault_overflow(): number {
  const a = 9007199254740991;
  return a + 1;
}

export function t_array_basics(): (number | string | undefined)[] {
  const xs = [10, 20, 30];
  return [xs.length, xs[0], xs[2], xs[3], xs[-1], "héllo😀".length];
}

export function t_array_spread(): number[] {
  const xs = [1, 2];
  const ys = [3];
  return [0, ...xs, ...ys, 4, ...[]];
}

export function t_includes(): boolean[] {
  const xs = ["a", "b"];
  return [xs.includes("a"), xs.includes("c"), [1, 2].includes(2), [].includes(1)];
}

function big(x: number): boolean {
  return x > 2;
}

export function t_callbacks(): (boolean | number | undefined | number[])[] {
  const xs = [1, 2, 3, 4];
  const k = 10;
  return [xs.some((x) => x > 3), xs.every((x) => x > 0), xs.find((x) => x > 2), xs.find((x) => x > 9),
    xs.filter(big), xs.map((x, i) => x * k + i), [].some(big), [].every(big)];
}

function byRank(a: Item, b: Item): number {
  if (a.rank !== b.rank) return a.rank > b.rank ? -1 : 1;
  return 0;
}

export function t_sort_stable(): Item[] {
  const items = [
    { id: 1, rank: 2, name: "a" }, { id: 2, rank: 3, name: "b" }, { id: 3, rank: 2, name: "c" },
    { id: 4, rank: 1, name: "d" }, { id: 5, rank: 3, name: "e" },
  ];
  return items.toSorted(byRank);
}

export function t_sort_arrow(): number[] {
  return [3, 1, 2, 1].toSorted((a, b) => a - b);
}

export function fault_inconsistent_comparator(): number[] {
  return [3, 1, 2].toSorted((a, b) => 1);
}

export function t_function_value(): number[] {
  const f = big;
  return [1, 5].filter(f).map((x) => x + 1);
}
