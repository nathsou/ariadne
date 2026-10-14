// Random JavaScript values for a type as `ariadne signatures` describes it, including values the type allows
// beyond the canonical encoding: records with extra fields in any order, optional fields absent or
// `undefined`, and either nullish value where a type admits both. Shared by the differential test and the
// validators' test.
export function values(seed) {
  const random = () => ((seed = (Math.imul(seed ^ (seed >>> 15), 0x2c1b3c6d) + 0x6d2b79f5) >>> 0) / 2 ** 32);
  const pick = xs => xs[Math.floor(random() * xs.length)];
  const chance = p => random() < p;
  const str = units => String.fromCharCode(...units);

  const bigints = [0n, 1n, -1n, 2n, -2n, 3n, 7n, -7n, 10n, 100n, -1000n, 2n ** 53n, -(2n ** 53n) - 1n, 2n ** 70n];
  const numbers = [0, 1, -1, 2, 3, 7, -7, 10, 100, -1000, 2 ** 31, 2 ** 53 - 1, -(2 ** 53 - 1)];
  const strings = ['', 'a', 'b', 'ab', 'aa', 'zero', 'positive', 'A', 'Z', ' ', ': ', 'é', '\u{1F600}', '\uD800', 'a\u0000',
    'm', 'n', 'ok', 'bad', 'legacy', 'none'];

  function value(ty) {
    switch (ty.t) {
      case 'bool': return chance(0.5);
      case 'bigint': return chance(0.4) ? BigInt(Math.floor(random() * 41) - 20) : pick(bigints);
      case 'number': return chance(0.5) ? Math.floor(random() * 41) - 20 : pick(numbers);
      case 'string': return pick(strings);
      case 'tag': return 'bool' in ty ? ty.bool : str(ty.value);
      case 'lits': return str(pick(ty.values));
      case 'option':
        if (chance(0.35)) return ty.nullish === 'null' ? null : ty.nullish === 'undef' ? undefined : pick([null, undefined]);
        return value(ty.of);
      case 'record': return record(ty.fields, []);
      case 'union': {
        const v = pick(ty.variants);
        return record(v.fields, [[ty.key, value(v.tag)]]);
      }
      case 'array': return Array.from({ length: Math.floor(random() * 5) }, () => value(ty.of));
      case 'map': return new Map(Array.from({ length: Math.floor(random() * 5) }, () => [pick(strings), value(ty.of)]));
      default: throw new Error(`no generator for ${JSON.stringify(ty)}`);
    }
  }

  /** A record: its fields in random order, optional fields sometimes absent, sometimes an extra field. */
  function record(fields, fixed) {
    const entries = [...fixed];
    for (const [name, ty] of fields) {
      if (ty.t === 'option' && ty.nullish !== 'null' && chance(0.3)) continue;
      entries.push([name, value(ty)]);
    }
    if (chance(0.2)) entries.push(['extra', pick(strings)]);
    for (let i = entries.length - 1; i > 0; i--) {
      const j = Math.floor(random() * (i + 1));
      [entries[i], entries[j]] = [entries[j], entries[i]];
    }
    return Object.fromEntries(entries);
  }

  return { random, pick, chance, value, record, strings };
}
