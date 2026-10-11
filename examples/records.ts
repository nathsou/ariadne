type Summary = { count: number; total: bigint; positive: boolean; };

export function demo(): Summary {
  const summary: Summary = { count: 0, total: 0n, positive: true };
  const values = [3n, -1n, 7n, 2n];
  for (let i = 0; i < values.length; i++) {
    const value = values[i] ?? 0n;
    summary.count = summary.count + 1;
    summary.total = summary.total + value;
    summary.positive = summary.positive && value > 0n;
  }
  return summary;
}
