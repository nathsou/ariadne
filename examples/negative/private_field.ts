// expected: A3004
class Box { private value = 1n; }
function f(): bigint { const box = new Box(); return box.value; }
