// Three-way scalar comparison: JavaScript, operational Lean, and extracted Lean.
// Also checks that modifying any new certificate link invalidates the artifact.
import { mkdir, mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/scalars.ts';

const cases = {
  abs: [[0n], [-1n], [9n], [-(10n ** 50n)]],
  update: [[2n, 9n, true], [2n, 9n, false], [-99n, 50n, true]],
  fallback: [[undefined], [0n], [-9n]],
  decimal: [[3, 2], [0, 0], [-0, 1], [Infinity, 2], [NaN, 3], [Number.MIN_VALUE, 1]],
  hello: [[''], ['world'], ['😀'], ['\ud800x\udfff']],
  optional: [[true, 7n], [false, 7n]],
  textBefore: [['a', 'b'], ['\uff00', '\u{10000}'], ['\ud800', '\udfff'], ['', '']],
  remainder: [[7, 3], [-7, 3], [-0, 2], [1, 0], [1, Infinity], [Infinity, 1], [NaN, 1]],
  scoped: [[0n], [-1n], [100000000000000000000n]],
  abs_denotes: [[]], CoreArtifacts: [[]],
  guarded: [[undefined, 7n], [0n, 7n], [-9n, 7n]],
  conjunction: [[undefined, 0n], [0n, 0n], [1n, 0n]],
  disjunction: [[undefined, 0n], [-1n, 0n], [0n, 0n]],
  ternary: [[undefined], [0n], [-2n]],
  forget: [[undefined, true], [undefined, false], [5n, true], [5n, false]],
  scopedTypes: [[0n], [-1n], [5n]],
};
const optionalInput = new Set(['fallback', 'guarded', 'conjunction', 'disjunction', 'ternary', 'forget']);
const optionalOutput = new Set(['optional', 'forget']);
const bits = n => {
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, Number.isNaN(n) ? NaN : n);
  return view.getBigUint64(0).toString();
};
const units = s => Array.from({ length: s.length }, (_, i) => s.charCodeAt(i));
function observe(x) {
  if (x === undefined) return ['undefined'];
  if (typeof x === 'bigint') return ['bigint', x.toString()];
  if (typeof x === 'number') return ['number', bits(x)];
  if (typeof x === 'string') return ['string', units(x)];
  return ['boolean', x];
}
function argument(x, option = false) {
  if (option) return x === undefined ? 'none' : `(some (${x} : Int))`;
  if (typeof x === 'bigint') return `(${x} : Int)`;
  if (typeof x === 'number') return `(Float.Model.ofBits ${bits(x)})`;
  if (typeof x === 'string') return `([${units(x)}] : JSString)`;
  return String(x);
}
function value(x) {
  if (x === undefined) return '.undefined';
  return `(.${typeof x === 'bigint' ? 'bigint' : typeof x === 'boolean' ? 'boolean' : typeof x} ${argument(x)})`;
}
const run = (command, args) => spawnSync(command, args, { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
const cli = args => run('.lake/build/bin/ariadne', args);
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-'));
try {
  let runner = 'import Examples.Shallow.scalars\nimport Ariadne.Observe\nopen Ariadne\n';
  const expected = [];
  for (const [name, inputs] of Object.entries(cases)) {
    for (const args of inputs) {
      const result = native[name](...args);
      expected.push({ ok: observe(result) }, { ok: observe(result) });
      const call = `(Extracted_scalars.Shallow.${name} ${args.map((x, i) => argument(x, i === 0 && optionalInput.has(name))).join(' ')})`;
      const encoded = optionalOutput.has(name) ? `(${call}.map Value.bigint).getD .undefined` :
        `.${typeof result === 'bigint' ? 'bigint' : typeof result === 'boolean' ? 'boolean' : typeof result} ${call}`;
      runner += `#eval IO.println ((observeResult (.ok ((${encoded}), {}))).compress)\n`;
      runner += `#eval IO.println ((observeResult (runState Extracted_scalars.program "${name}" 100 [${args.map(value)}])).compress)\n`;
    }
  }
  const runnerPath = resolve(dir, 'Compare.lean');
  await writeFile(runnerPath, runner);
  const compared = run('lake', ['env', 'lean', runnerPath]);
  assert.equal(compared.status, 0, compared.stdout + compared.stderr);
  assert.deepEqual(compared.stdout.trim().split('\n').map(JSON.parse), expected);

  const source = resolve(dir, 'input.ts');
  const artifact = resolve(dir, 'Output.lean');
  const branches = 20;
  await writeFile(source, `function branch(flag: boolean): bigint { let total = 0n; ${
    'if (flag) { total += 1n; } else { total -= 1n; } '.repeat(branches)
  } return total; }`);
  const joined = cli(['extract', source, '--out', artifact, '--namespace', 'Joined']);
  assert.equal(joined.status, 0, joined.stdout + joined.stderr);
  const joinedText = await readFile(artifact, 'utf8');
  assert.ok(joinedText.length < 300000, 'sequential branches must share their continuation');
  await writeFile(artifact, joinedText + `\nexample : Joined.Shallow.branch true = ${branches} := by kernel_rfl\n` +
    `example : Joined.Shallow.branch false = -${branches} := by kernel_rfl\n`);
  const checkedJoins = run('lake', ['env', 'lean', artifact]);
  assert.equal(checkedJoins.status, 0, checkedJoins.stdout + checkedJoins.stderr);
  for (const [text, code] of [
    ['function f(): bigint { while (true) {} return 0n; }', 'A5101'],
    ['function f(n: bigint): bigint { for (let i = 0n; i < n; i += 1n) { n -= 1n; } return n; }', 'A5101'],
    ['function f(n: bigint): bigint { for (let i = 0n; i < n; i += 1n) { i += 1n; } return n; }', 'A5101'],
    ['function f(x: { value: number }): number { return x.value; }', 'A5102'],
    ['function f(m: Map<string, bigint>): void { m = new Map<string, bigint>(); m.set("x", 1n); }', 'A5102'],
    ['function f(xs: bigint[]): void { xs = []; xs.push(1n); }', 'A5102'],
    ['function bump(m: Map<string, bigint>): bigint { m.set("x", 1n); return 1n; } function f(m: Map<string, bigint>): bigint { return 1n + bump(m); }', 'A5102'],
    ['function f(x: bigint): bigint { return x / 2n; }', 'A5104'],
    ['type Int53 = number; function f(x: Int53): number { return Math.sqrt(x); }', 'A5104'],
  ]) {
    await writeFile(source, text);
    await writeFile(artifact, 'preserve existing output\n');
    const rejected = cli(['extract', source, '--out', artifact, '--json']);
    assert.equal(rejected.status, 1, rejected.stdout + rejected.stderr);
    assert.equal(JSON.parse(rejected.stdout).code, code);
    assert.equal(await readFile(artifact, 'utf8'), 'preserve existing output\n');
  }
  await writeFile(source, 'function constant(): bigint { return 3n; }');
  const extracted = cli(['extract', source, '--out', artifact, '--namespace', 'Tamper']);
  assert.equal(extracted.status, 0, extracted.stdout + extracted.stderr);
  const good = await readFile(artifact, 'utf8');
  for (const bad of [
    good.replace('return 3n;', 'return 4n;'),
    good.replace('Core.Term.int (3)', 'Core.Term.int (4)'),
    good.replace('(3 : _root_.Int)', '(4 : _root_.Int)'),
  ]) {
    assert.notEqual(bad, good);
    await writeFile(artifact, bad);
    const rejected = run('lake', ['env', 'lean', artifact]);
    assert.notEqual(rejected.status, 0, 'modified source, Core or native definition must fail');
    assert.ok(rejected.stdout.includes('error'), rejected.stdout + rejected.stderr);
  }
  console.log(`Shallow extraction passed: ${expected.length / 2} three-way comparisons, refusals, and three certificate tamper checks.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
