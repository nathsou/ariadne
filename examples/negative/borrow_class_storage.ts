// expected: A3001
class Box { items: readonly bigint[] = []; constructor(xs: readonly bigint[]) { this.items = xs; } }
