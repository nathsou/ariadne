// expected: A3001
type Int53 = number;
type Narrow = { value: Int53 };
function assignHalf(input: { value: number }): void { input.value = 0.5; }
export function corrupt(input: Narrow): void { assignHalf(input); }
