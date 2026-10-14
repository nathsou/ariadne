// Model validation: string methods, division and remainder.
export function t_starts(): boolean[] {
  return ["abc".startsWith("ab"), "abc".startsWith(""), "abc".startsWith("abcd"), "".startsWith(""), "abc".startsWith("b")];
}

export function t_ends(): boolean[] {
  return ["abc".endsWith("bc"), "abc".endsWith(""), "abc".endsWith("xabc"), "".endsWith("a")];
}

export function t_includes(): boolean[] {
  return ["abcabc".includes("ca"), "abc".includes(""), "".includes(""), "abc".includes("cb"), "aab".includes("ab")];
}

export function t_index_of(): number[] {
  return ["abcabc".indexOf("ca"), "abc".indexOf(""), "".indexOf(""), "abc".indexOf("cb"), "aab".indexOf("ab"), "😀x".indexOf("x")];
}

export function t_slice(): string[] {
  const s = "abcdef";
  return [s.slice(0), s.slice(2), s.slice(-2), s.slice(-10), s.slice(10), s.slice(1, 3), s.slice(3, 1), s.slice(-3, -1),
    s.slice(1, -1), s.slice(-1, 10), s.slice(0, 0), "".slice(0, 2), "😀".slice(1)];
}

export function t_floor_div(): number[] {
  return [Math.floor(7 / 2), Math.floor(-7 / 2), Math.floor(7 / -2), Math.floor(-7 / -2), Math.floor(6 / 3), Math.floor(0 / 5),
    Math.floor(9007199254740991 / 2), Math.floor(-9007199254740991 / 3), Math.floor(9007199254740991 / 9007199254740990),
    Math.floor(9007199254740990 / 9007199254740991), Math.floor(-1 / 9007199254740991)];
}

export function t_mod(): number[] {
  return [7 % 2, -7 % 2, 7 % -2, -7 % -2, 6 % 3, 9007199254740991 % 2, -9007199254740991 % 1000, 5 % 9007199254740991];
}

export function t_bigint_div(): bigint[] {
  return [7n / 2n, -7n / 2n, 7n / -2n, -7n / -2n, 1180591620717411303424n / 3n, 7n % 2n, -7n % 2n, 7n % -2n, -1180591620717411303424n % 7n];
}

export function fault_div_zero(): number {
  return Math.floor(1 / 0);
}

export function fault_mod_zero(): number {
  return 1 % 0;
}

export function fault_bigint_div_zero(): bigint {
  return 1n / 0n;
}

export function fault_number_div(): number {
  return 6 / 3;
}
