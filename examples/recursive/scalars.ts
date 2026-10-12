// Nested user calls, conversions, binary64 builtins, and string methods.
export function scalars(text: string, index: number): bigint {
  const clipped = text.slice(1, text.length);
  const code = clipped.charCodeAt(index);
  if (Number.isNaN(code)) { return -1n; }
  return twice(BigInt(Math.floor(Math.sqrt(code))));
}
function twice(value: bigint): bigint {
  value = value + value;
  return value;
}
