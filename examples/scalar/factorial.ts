export function factorial(count: bigint): bigint {
  let product = 1n;
  while (count > 1n) {
    product = product * count;
    count = count - 1n;
  }
  return product;
}
