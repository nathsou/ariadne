// expected: A1001
function f(a: boolean | undefined): boolean { return a ?? true || false; }
