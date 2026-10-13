// expected: A1001
export function f(message: string): bigint {
  throw new Error(message);
}
