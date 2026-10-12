// expected: A3002
function f(): void {
  let total = 0;
  const xs = [1];
  xs.map((x: number) => { total += x; return x; });
}
