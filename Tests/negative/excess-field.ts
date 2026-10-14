// expect: A2002
interface P { x: bigint }
export function f(): P {
  return { x: 1n, y: 2n };
}
