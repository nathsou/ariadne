type Int53 = number;
export function nested(flag: boolean, x: Int53): Int53 {
  if (flag) { { const y = x + 1; x = y * 2; } }
  else { x -= 1; }
  return x * 3;
}
