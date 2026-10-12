import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/arrays.ts';

const cases = {
  transform: [[[], 9n], [[-2n, 0n, 5n], 3n], [[10n ** 40n], -1n]],
  sum: [[[]], [[-9n, 5n, 4n]], [[10n ** 40n, 7n]]],
  indexed: [[[]], [[1, 2, 3]], [[Infinity]], [[-0, -0]], [[NaN]]],
  find: [[[], 0n], [[-3n, 2n, 5n], 0n], [[1n], 9n]],
  findIndex: [[[], 0n], [[-3n, 2n, 5n], 0n], [[1n], 9n]],
  allPositive: [[[]], [[1n, 2n]], [[1n, 0n]], [[-1n]]],
  anyPositive: [[[]], [[-1n, 0n]], [[-1n, 2n]]],
  lookup: [[[], 0], [[7n, 9n], -0], [[7n, 9n], 1], [[7n], -1], [[7n], 0.5],
    [[7n], NaN], [[7n], Infinity], [[7n], -Infinity]],
  sliced: [[[1n, 2n, 3n], -2, Infinity], [[1n, 2n, 3n], NaN, -1],
    [[1n, 2n], 0.9, 1.9], [[1n, 2n], -Infinity, Infinity], [[1n], Infinity, -Infinity]],
  copy: [[[]], [[1n, 2n]]], combined: [[[]], [[5n, 6n]]],
  constantMap: [[[]], [[1n, 2n]]], count: [[[]], [[1n, 2n]]],
  score: [[[]], [[5n, 6n]]], empty: [[]],
  program: [[9n]], Int: [[[1n, 2n]]], afterNames: [[[1n, 2n]]],
};
const arrayResults = new Set(['transform', 'sliced', 'copy', 'combined', 'constantMap', 'empty', 'Int']);
const optionResults = new Set(['find', 'lookup']);
const bits = value => {
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, Number.isNaN(value) ? NaN : value);
  return view.getBigUint64(0).toString();
};
function argument(value) {
  if (Array.isArray(value)) return `[${value.map(argument)}]`;
  if (typeof value === 'number') return `(Float.Model.ofBits ${bits(value)})`;
  return `(${value} : Int)`;
}
function scalar(value) {
  return `(.${typeof value === 'number' ? 'number' : 'bigint'} ${argument(value)})`;
}
function observe(value) {
  if (Array.isArray(value)) return ['array', value.map(observe)];
  if (value === undefined) return ['undefined'];
  if (typeof value === 'bigint') return ['bigint', value.toString()];
  if (typeof value === 'number') return ['number', bits(value)];
  return ['boolean', value];
}
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-arrays-'));
try {
  let runner = 'import Examples.Shallow.arrays\nimport Ariadne.Observe\nopen Ariadne\n';
  const expected = [];
  for (const [name, inputs] of Object.entries(cases)) {
    for (const args of inputs) {
      const before = structuredClone(args);
      const result = native[name](...args);
      assert.deepEqual(args, before, `${name} must preserve readonly inputs`);
      expected.push({ ok: observe(result) }, { ok: observe(result) });
      const call = `(Extracted_arrays.Shallow.${name} ${args.map(argument).join(' ')})`;
      const shallow = arrayResults.has(name) ?
        `(.ref 0, { heap := [.array (${call}.map Value.bigint)] })` :
        optionResults.has(name) ? `((${call}.map Value.bigint).getD .undefined, {})` :
        `(.${typeof result === 'bigint' ? 'bigint' : typeof result === 'boolean' ? 'boolean' : 'number'} ${call}, {})`;
      runner += `#eval IO.println ((observeResult (.ok ${shallow})).compress)\n`;
      const hasArray = Array.isArray(args[0]);
      const heap = hasArray ? `{ heap := [.array [${args[0].map(scalar)}]] }` : '{}';
      const encoded = hasArray ? ['.ref 0', ...args.slice(1).map(scalar)] : args.map(scalar);
      runner += `#eval IO.println ((observeResult (Ariadne.apply Extracted_arrays.program 1000 ${heap} (.function "${name}") [${encoded}])).compress)\n`;
    }
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').map(JSON.parse), expected);
  console.log(`Shallow arrays passed: ${expected.length / 2} three-way comparisons with readonly input preservation.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
