// Test-only harness: runs every exported function of each V2 fixture in Bun (or Node)
// and in the trusted model (`ariadne2 batch`) on the same inputs and compares the
// observations. Inputs are generated from the checker's resolved parameter types,
// including JavaScript values the types allow beyond the canonical encoding:
// records with extra fields in any order, optional fields absent or `undefined`,
// either nullish value where a type admits both, and omitted trailing arguments.
import { readdir } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { observe } from './v2-observe.mjs';

const cli = resolve('.lake/build/bin/ariadne2');
const dir = resolve(process.argv[2] ?? 'V2Tests/fixtures');
const perFunction = Number(process.argv[3] ?? 300);

let seed = 0x2545f491;
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

let calls = 0;
let failures = 0;
for (const file of (await readdir(dir)).filter(f => f.endsWith('.ts')).sort()) {
  const path = resolve(dir, file);
  const signatures = spawnSync(cli, ['signatures', path], { encoding: 'utf8' });
  if (signatures.status !== 0) throw new Error(`${file}: ${signatures.stderr}`);
  const module = await import(pathToFileURL(path).href);
  const lines = [];
  const expected = [];
  for (const sig of signatures.stdout.trim().split('\n').map(l => JSON.parse(l))) {
    if (!sig.exported) continue;
    for (let i = 0; i < perFunction; i++) {
      let args = sig.params.map(value);
      // Omit trailing arguments that may be undefined.
      while (args.length > 0 && args[args.length - 1] === undefined && chance(0.5)) args = args.slice(0, -1);
      let result;
      try { result = observe(module[sig.name](...args)); } catch (e) { result = ['throws', String(e)]; }
      lines.push(JSON.stringify([sig.name, ...args.map(observe)]));
      expected.push({ call: `${sig.name}(${args.map(a => observeText(a)).join(', ')})`, result });
    }
  }
  const run = spawnSync(cli, ['batch', path], { input: lines.join('\n') + '\n', encoding: 'utf8', maxBuffer: 1 << 28 });
  if (run.status !== 0) throw new Error(`${file}: ${run.stderr}`);
  const actual = run.stdout.trim().split('\n').map(l => JSON.parse(l));
  expected.forEach(({ call, result }, i) => {
    calls++;
    if (JSON.stringify(actual[i]) !== JSON.stringify(result)) {
      failures++;
      if (failures <= 20) console.error(`${file}: ${call}:\n  js    ${JSON.stringify(result)}\n  model ${JSON.stringify(actual[i])}`);
    }
  });
}

function observeText(v) {
  return JSON.stringify(v, (_, x) => (typeof x === 'bigint' ? `${x}n` : x === undefined ? '<undefined>' : x));
}

if (failures > 0) {
  console.error(`V2 differential: ${failures} of ${calls} calls disagree.`);
  process.exit(1);
}
console.log(`V2 differential passed: ${calls} calls.`);
