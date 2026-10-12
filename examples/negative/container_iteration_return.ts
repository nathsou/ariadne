// expected: A3001
function f(rows: bigint[][]): bigint[] { for (const row of rows) { return row; } return []; }
