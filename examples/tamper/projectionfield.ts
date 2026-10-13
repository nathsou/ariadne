type Row = { count: number };

export function increment(rows: Row[], index: number): void {
  rows[index].count++;
}
