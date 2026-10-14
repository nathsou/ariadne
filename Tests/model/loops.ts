// Model validation: let, assignment, loops, break and continue.
export function t_sum(): number {
  let total = 0;
  for (const x of [1, 2, 3, 4]) {
    if (x === 2) continue;
    if (x === 4) break;
    total += x;
  }
  return total;
}

export function t_entries(): number[] {
  let out: number[] = [];
  for (const [i, x] of [5, 6, 7].entries()) {
    out = [...out, i * 10 + x];
  }
  return out;
}

export function t_nested(): string {
  let s = "";
  for (const a of ["x", "y"]) {
    for (const b of ["1", "2", "3"]) {
      if (b === "2") continue;
      if (a === "y" && b === "3") break;
      s = s + a + b;
    }
    s = s + ";";
  }
  return s;
}

export function t_return_in_loop(): number {
  for (const [i, x] of [3, 8, 9].entries()) {
    if (x > 5) return i;
  }
  return -1;
}

export function t_switch_in_loop(): string {
  let s = "";
  for (const k of ["a", "b", "c", "d"]) {
    switch (k) {
      case "a":
        continue;
      case "b":
        s = s + "B";
        break;
      case "c": {
        const t = k + k;
        s = s + t;
        break;
      }
      default:
        s = s + "!";
    }
    s = s + ".";
  }
  return s;
}

export function t_block_scope(): number {
  let x = 1;
  {
    const y = 2;
    x = x + y;
  }
  if (x > 0) x = x * 10;
  else x = 0;
  return x;
}

export function t_param_assign(): number {
  return bump(4);
}

function bump(n: number): number {
  n = n + 1;
  return n;
}
