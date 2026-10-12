export function shortCircuit(enabled: boolean): boolean {
  return enabled && fail();
}
function fail(): boolean {
  const impossible = 1n / 0n;
  return impossible === 0n;
}
