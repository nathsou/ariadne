// expected: A3004
function g(): bigint { return 1n; } function f(): bigint { const g = 2n; return g(); }
