type Row = { count: number };

export function addCount(rows: Row[], index: number, value: number): void {
  rows[index].count += value;
}
