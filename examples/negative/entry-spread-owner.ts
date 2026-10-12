// expected: A3001
function duplicate(): void {
  const values = new Map<string, bigint[]>();
  values.set('a', [1n]);
  const entries = [...values.entries()];
}
