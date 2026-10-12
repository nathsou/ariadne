export function sum(xs: readonly bigint[]): bigint {
  let total = 0n;
  for (const x of xs) { total += x; }
  return total;
}

export function until(xs: readonly bigint[], limit: bigint): bigint {
  let total = 0n;
  for (const x of xs) {
    if (x < 0n) { continue; }
    if (x > limit) { break; }
    total += x;
  }
  return total;
}

export function first(xs: readonly bigint[], floor: bigint): bigint | undefined {
  for (const x of xs) {
    if (x >= floor) { return x; }
  }
  return undefined;
}

export function nested(xs: readonly bigint[], ys: readonly bigint[]): bigint {
  let total = 0n;
  for (const x of xs) {
    if (x < 0n) { continue; }
    for (const y of ys) {
      if (y < 0n) { break; }
      if (y === 0n) { continue; }
      if (x + y > 100n) { return total; }
      total += x * y;
    }
    total += 1n;
  }
  return total;
}

export function last(xs: readonly bigint[]): bigint | undefined {
  let found: bigint | undefined = undefined;
  for (const x of xs) {
    if (found === undefined || x > found) { found = x; }
  }
  return found;
}

export function localScope(xs: readonly bigint[]): bigint {
  let total = 0n;
  for (let x of xs) {
    const temporary = x + 1n;
    x = temporary * 2n;
    total += x;
  }
  const temporary = total + 3n;
  return temporary;
}

export function nestedNoReturn(xs: readonly bigint[]): bigint {
  let total = 0n;
  for (const x of xs) {
    for (const y of xs) {
      if (y < 0n) { continue; }
      total += x * y;
    }
    if (total > 100n) { break; }
  }
  return total;
}

export function switched(xs: readonly bigint[]): bigint {
  let total = 0n;
  for (const x of xs) {
    switch (x) {
      case 0n: continue;
      default: total += x; break;
      case 1n: total += 10n; break;
      case 2n: return total;
    }
    total += 1n;
  }
  return total;
}

export function noDefault(x: bigint): bigint {
  let result = 1n;
  switch (x) {
    case 0n:
      for (const y of [2n, 3n]) {
        if (y > 2n) { break; }
        result += y;
      }
      break;
    case 1n: result += 10n; break;
  }
  return result;
}

export function counted(start: bigint, stop: bigint): bigint {
  let total = 0n;
  for (let i = start; i < stop; i += 1n) { total += i; }
  return total;
}

export function countedExits(stop: bigint): bigint {
  let total = 0n;
  for (let i = -3n; i < stop; i += 1n) {
    if (i < 0n) { continue; }
    if (i === 7n) { return total; }
    if (i > 10n) { break; }
    total += i;
  }
  return total;
}

export function switchReturn(x: bigint): bigint {
  switch (x) {
    case 0n: return 10n;
    default: return 20n;
  }
}
