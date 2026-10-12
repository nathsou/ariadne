// Division truncates toward zero and throws on a zero denominator.
export function quotient(numerator: bigint, denominator: bigint): bigint {
  return numerator / denominator;
}
