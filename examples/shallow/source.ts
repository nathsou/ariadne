export function arithmetic(x: bigint, y: bigint): bigint { return -(x + y) * (x - y); }
export function quotient(x: number, y: number): number { return (x * y) / (x + y); }
export function choice(flag: boolean, x: bigint, y: bigint): bigint { return flag ? x : y; }
// This user name must not collide with the generated source theorem for choice.
export function choice_source(): bigint { return 7n; }
export function conjunction(a: boolean, b: boolean): boolean { return a && !b; }
export function disjunction(a: boolean, b: boolean): boolean { return a || !b; }
export function compare(x: bigint, y: bigint): boolean { return x <= y; }
export function equal(x: string, y: string): boolean { return x === y; }
export function text(name: string): string { return 'hello ' + name; }
export function unit(): void { return; }
