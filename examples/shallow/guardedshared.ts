type Int53 = number;
export function nested(flag: boolean, x: Int53): Int53 {
  if (flag) { { const y = x + 1; x = y * 2; } }
  else { x -= 1; }
  return x * 3;
}
export function flattened(flag: boolean, x: Int53): Int53 {
  { x = x + 1; }
  if (flag) { x = x * 2; } else { x = x - 2; }
  return x;
}
export function nestedFlattened(flag: boolean, x: Int53): Int53 {
  if (flag) {
    { x = x + 1; }
    { const y = x * 2; x = y; }
  } else { x = x - 1; }
  return x;
}
export function early(flag: boolean, x: Int53): Int53 {
  if (flag) { { const y = x + 1; x = y; } return x; }
  { x = x - 1; }
  return x;
}
export function empty(x: Int53): Int53 { {} { {} } return x; }

export function innerJoin(a: boolean, b: boolean, x: Int53): Int53 {
  if (a) { if (b) { x = x + 1; } else { x = x - 1; } x = x * 2; }
  else { x = x + 3; }
  return x * 4;
}
export function branchArithmetic(flag: boolean, x: Int53, y: Int53): Int53 {
  if (flag) { x = x + y; } else { x = x - y; }
  return x * y;
}
export function mathScoped(flag: boolean, x: Int53): Int53 {
  { const y: Int53 = Math.abs(x); x = y; }
  if (flag) { x = x + 1; } else { x = x - 1; }
  return x;
}
