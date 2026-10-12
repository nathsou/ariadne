// expected: A2010
function missing(x: bigint): bigint {
  switch (x) {
    default: break; return 1n;
  }
}
