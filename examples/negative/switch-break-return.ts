// expected: A2010
function missing(x: bigint): bigint {
  switch (x) {
    default:
      if (x > 0n) { break; }
      return 1n;
  }
}
