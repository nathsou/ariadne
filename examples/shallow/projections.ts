type Row = { count: number };

export function incrementElement(values: number[], index: number): void {
  values[index]++;
}

export function appendGroup(groups: Map<string, bigint[]>, key: string, value: bigint): void {
  groups.get(key)!.push(value);
}

export function appendRow(rows: bigint[][], index: number, value: bigint): void {
  rows[index].push(value);
}

export function increment(rows: Row[], index: number): void {
  rows[index].count++;
}

export function addCount(rows: Row[], index: number, value: number): void {
  rows[index].count += value;
}

export function setCount(groups: Map<string, Row>, key: string, value: number): void {
  groups.get(key)!.count = value;
}
