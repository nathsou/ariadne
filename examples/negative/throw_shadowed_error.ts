// expected: A3004
class Error {
  readonly message: string = "shadowed";
}

export function f(): bigint {
  throw new Error("x");
}
