// Test-only harness: runs every exported function of each V2 fixture in Node and in
// the trusted model (`ariadne2 batch`) on the same inputs and compares the results.
// Node >= 22.18 imports the TypeScript fixtures directly (type stripping).
import { readdir } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const cli = resolve('.lake/build/bin/ariadne2');
const dir = resolve(process.argv[2] ?? 'V2Tests/fixtures');
const perFunction = Number(process.argv[3] ?? 400);

let seed = 0x2545f491;
const random = () => ((seed = (Math.imul(seed ^ (seed >>> 15), 0x2c1b3c6d) + 0x6d2b79f5) >>> 0) / 2 ** 32);
const pick = xs => xs[Math.floor(random() * xs.length)];

const pools = {
  bigint: [0n, 1n, -1n, 2n, -2n, 3n, 7n, -7n, 10n, 100n, -1000n, 2n ** 53n, -(2n ** 53n) - 1n, 2n ** 70n, -(2n ** 70n)],
  boolean: [true, false],
  string: ['', 'a', 'b', 'ab', 'aa', 'zero', 'positive', 'A', 'Z', ' ', ': ', 'é', '\u{1F600}', '\uD800', '\uDC00x', 'a\u0000', 'ab\u{10FFFF}'],
};
const generate = type => {
  if (type === 'bigint' && random() < 0.3) return BigInt(Math.floor(random() * 41) - 20);
  return pick(pools[type]);
};

const units = s => Array.from({ length: s.length }, (_, i) => s.charCodeAt(i));
const encode = (type, v) => type === 'bigint' ? `i:${v}` : type === 'boolean' ? `b:${v}` : `s:${units(v).join(',')}`;
const observe = v => {
  switch (typeof v) {
    case 'undefined': return 'undefined';
    case 'bigint': return `bigint:${v}`;
    case 'boolean': return `bool:${v}`;
    case 'string': return `string:[${units(v).join(',')}]`;
    default: throw new Error(`unexpected result ${typeof v}`);
  }
};

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
      const args = sig.params.map(generate);
      let result;
      try { result = observe(module[sig.name](...args)); } catch (e) { result = 'error'; }
      lines.push([sig.name, ...args.map((v, k) => encode(sig.params[k], v))].join('\t'));
      expected.push({ call: `${sig.name}(${args.map(a => JSON.stringify(typeof a === 'bigint' ? `${a}n` : a)).join(', ')})`, result });
    }
  }
  const run = spawnSync(cli, ['batch', path], { input: lines.join('\n') + '\n', encoding: 'utf8', maxBuffer: 1 << 28 });
  if (run.status !== 0) throw new Error(`${file}: ${run.stderr}`);
  const actual = run.stdout.trim().split('\n');
  expected.forEach(({ call, result }, i) => {
    const model = actual[i];
    const agrees = result === 'error' ? model?.startsWith('error:') : model === result;
    if (!agrees) {
      failures++;
      if (failures <= 20) console.error(`${file}: ${call}: node ${result}, model ${model}`);
    }
    calls++;
  });
}
if (failures > 0) {
  console.error(`V2 differential: ${failures} of ${calls} calls disagree.`);
  process.exit(1);
}
console.log(`V2 differential passed: ${calls} calls.`);
