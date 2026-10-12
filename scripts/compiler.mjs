// Differential and adversarial tests for the proof-carrying scalar backend.
// Uses only the JavaScript host's built-in modules.
import { mkdir, mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import assert from 'node:assert/strict';

const cases = {
  multiply: [[7n, 13n], [-9n, 20n], [100000000000000000000n, 9n], [9n, -3n], [3n, 0n]],
  triangular: [[0n], [1n], [20n], [-7n]],
  factorial: [[0n], [1n], [10n], [30n], [-3n]],
  gcd: [[0n, 0n], [270n, 192n], [-54n, 24n], [24n, -54n], [999n, 0n]],
  reverse: [[''], ['a'], ['racecar'], ['A😀B'], ['\ud800x\udfff']],
  boundedSum: [[20n, 9n], [9n, 20n], [20n, 0n], [-1n, 5n]],
  choose: [[true, undefined], [true, ''], [true, 'hello'], [false, 'ignored']],
  findUnit: [['hello', 'l'], ['', 'x'], ['abc', 'z'], ['A😀B', '\ude00']],
  quotient: [[7n, 3n], [-7n, 3n], [7n, -3n], [-7n, -3n], [1n, 0n]],
  numberEdges: [[5.5, 2], [-5.5, 2], [-0, 1], [0, 1], [1, 0], [Infinity, 2],
    [2, Infinity], [NaN, 2], [Number.MIN_VALUE, 2], [2 ** 53, 3]],
};

function bits(value) {
  const bytes = new DataView(new ArrayBuffer(8));
  bytes.setFloat64(0, Number.isNaN(value) ? NaN : value);
  return bytes.getBigUint64(0).toString();
}
const units = value => Array.from({ length: value.length }, (_, i) => value.charCodeAt(i));
function observe(value) {
  if (value === undefined) return ['undefined'];
  if (typeof value === 'bigint') return ['bigint', value.toString()];
  if (typeof value === 'number') return ['number', bits(value)];
  if (typeof value === 'string') return ['string', units(value)];
  if (typeof value === 'boolean') return ['boolean', value];
  throw new Error('Unsupported test value');
}
function lean(value) {
  if (value === undefined) return '.undefined';
  if (typeof value === 'bigint') return `(.bigint (${value}))`;
  if (typeof value === 'number') return `(.number (Float.Model.ofBits ${bits(value)}))`;
  if (typeof value === 'string') return `(.string [${units(value).join(', ')}])`;
  if (typeof value === 'boolean') return `(.boolean ${value})`;
  throw new Error('Unsupported test value');
}
const run = (cmd, args) => spawnSync(cmd, args, { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
const cli = args => run('.lake/build/bin/ariadne', args);
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/compiler-'));
try {
  let runner = Object.keys(cases).map(name => `import Examples.Compiled.${name}`).join('\n');
  runner += '\nimport Ariadne.Observe\nopen Ariadne\n';
  const expected = [];
  for (const [name, inputs] of Object.entries(cases)) {
    const module = await import(pathToFileURL(resolve(`examples/scalar/${name}.ts`)).href);
    for (const args of inputs) {
      try {
        expected.push({ ok: observe(module[name](...args)) });
      } catch (error) {
        assert.ok(error instanceof RangeError);
        expected.push({ error: 'Ariadne.Fault.rangeError "bigint division by zero"' });
      }
      runner += `#eval IO.println ((observeResult ((Compiled_${name}.compiled_ts_${name} 1000 ` +
        `[${args.map(lean).join(', ')}]).map (fun v => (v, {})))).compress)\n`;
    }
  }
  const runnerPath = resolve(dir, 'Differential.lean');
  await writeFile(runnerPath, runner);
  const result = run('lake', ['env', 'lean', runnerPath]);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  const actual = result.stdout.trim().split('\n').map(line => JSON.parse(line));
  assert.deepEqual(actual, expected);

  const source = resolve(dir, 'input.ts');
  const artifact = resolve(dir, 'Output.lean');
  const unsupported = [
    ['function helper(): bigint { return 1n; } export function demo(): bigint { return helper(); }', 'A4101', 'helper()'],
    ['export function demo(): number { const xs = [1]; return xs.length; }', 'A4101', '[1]'],
    ['export function demo(xs: number[]): number { return xs.length; }', 'A4101', 'xs'],
    ['export function demo(): bigint { const m = new Map<string, bigint>(); return 0n; }', 'A4101', 'Map'],
    ['export function demo(): number { return Math.abs(-1); }', 'A4101', 'Math.abs'],
  ];
  for (const [text, code, highlighted] of unsupported) {
    await writeFile(source, text);
    await writeFile(artifact, 'preserve existing output\n');
    const failed = cli(['compile', source, 'demo', '--out', artifact, '--json']);
    assert.equal(failed.status, 1, failed.stdout + failed.stderr);
    const diagnostic = JSON.parse(failed.stdout);
    assert.equal(diagnostic.code, code);
    assert.ok(text.slice(diagnostic.startByte, diagnostic.endByte).includes(highlighted), failed.stdout);
    assert.equal(await readFile(artifact, 'utf8'), 'preserve existing output\n');
  }
  await writeFile(source, 'export function demo(): bigint { return 0n; }');
  const missing = cli(['compile', source, 'missing', '--out', artifact, '--json']);
  assert.equal(missing.status, 1);
  assert.equal(JSON.parse(missing.stdout).code, 'A4103');
  assert.equal(cli(['compile', source, '--out', artifact]).status, 2);
  assert.equal(cli(['compile', source, 'demo', '--out', artifact, '--json', '--json']).status, 2);
  const compiled = cli(['compile', source, 'demo', '--out', artifact]);
  assert.equal(compiled.status, 0, compiled.stdout + compiled.stderr);
  const good = await readFile(artifact, 'utf8');
  const bad = good.replace('Target.literal (Ariadne.Literal.bigint 0)', 'Target.literal (Ariadne.Literal.bigint 1)');
  assert.notEqual(bad, good);
  await writeFile(artifact, bad);
  const rejected = run('lake', ['env', 'lean', artifact]);
  assert.notEqual(rejected.status, 0, 'modified target code must invalidate compilation_checked');
  assert.ok(rejected.stdout.includes('kernel'), rejected.stdout + rejected.stderr);
  console.log(`Scalar compilation passed: ${expected.length} native comparisons, diagnostics, and target-tampering rejection.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
