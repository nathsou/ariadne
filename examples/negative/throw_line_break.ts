// expected: A1005
export function f(): bigint {
  throw
    new Error("late");
}
