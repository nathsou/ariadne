import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/collections.ts';

const cases = {
  histogram: [[[]], [['a', 'b', 'a']], [['\ud800', '\0', '\ud800']]],
  ordered: [[[]], [['a', 'remove', 'b', 'a']], [['remove', 'a']]],
  numericSet: [[[]], [[-0, 0, NaN, NaN, 1, -1, Infinity, -Infinity]], [[3, 2, 3]]],
  numericMap: [[[]], [[-0, 0, NaN, NaN, 1, -1, Infinity]], [[2, 1, 2, 1]]],
  flags: [[[]], [[true, false, true]], [[false]]],
  unique: [[[], 0n], [[1n, 2n, 1n], 1n], [[10n ** 40n, -1n], 9n]],
  entries: [[[]], [['a', 'b', 'a']], [['skip', 'skip', 'ok']]],
  setEntries: [[[]], [[1n, 2n, 1n]], [[-1n, 9n]]],
  collect: [[[]], [[1n, -3n, 2n]], [[-1n, -2n]]],
  clear: [[[], false], [['a', 'a', 'b'], false], [['a', 'b'], true]],
  read: [[new Map(), 'a'], [new Map([['a', 7n]]), 'a'], [new Map([['a', 7n]]), 'b']],
  readDefault: [[new Map(), 'a'], [new Map([['a', 7n]]), 'a']],
  numericHas: [[[NaN, 0], NaN, NaN], [[NaN], 0, NaN], [[-0, 0], -0, 0], [[-0, NaN], 1, 0]],
  numericDelete: [[[NaN, -0, 1], NaN], [[1, -0, NaN], 0], [[-0, 1], 9]],
  nestedValues: [['a'], ['b']], entryValues: [[[]], [['a', 'b', 'a']]],
  entrySizes: [[[]], [['a', 'b', 'a']]], tupleSize: [[]],
};
const outputs = {
  histogram: ['map', 'string', 'bigint'], ordered: ['array', 'string'],
  numericSet: ['array', 'number'], numericMap: ['map', 'number', 'bigint'],
  unique: ['array', 'bigint'], collect: ['array', 'bigint'], read: ['option', 'bigint'],
  numericDelete: ['array', 'number'], nestedValues: ['array', 'bigint'], entryValues: ['array', 'bigint'],
  entrySizes: ['array', 'number'],
};
const units = value => Array.from({ length: value.length }, (_, i) => value.charCodeAt(i));
const bits = value => {
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, Number.isNaN(value) ? NaN : value);
  return view.getBigUint64(0).toString();
};
function argument(value) {
  if (Array.isArray(value)) return `[${value.map(argument)}]`;
  if (value instanceof Map) {
    return [...value].reduce((m, [k, v]) => `(Ariadne.Shallow.JSMap.set ${m} ${argument(k)} ${argument(v)})`,
      '(Ariadne.Shallow.JSMap.empty : Ariadne.Shallow.JSMap JSString Int)');
  }
  if (typeof value === 'string') return `([${units(value)}] : JSString)`;
  if (typeof value === 'number') return `(Float.Model.ofBits ${bits(value)})`;
  if (typeof value === 'boolean') return String(value);
  return `(${value} : Int)`;
}
const scalar = value => `(Value.${typeof value === 'boolean' ? 'boolean' : typeof value} ${argument(value)})`;
function observe(value) {
  if (Array.isArray(value)) return ['array', value.map(observe)];
  if (value instanceof Map) return ['map', [...value].map(([k, v]) => [observe(k), observe(v)])];
  if (value === undefined) return ['undefined'];
  if (typeof value === 'string') return ['string', units(value)];
  if (typeof value === 'number') return ['number', bits(value)];
  if (typeof value === 'bigint') return ['bigint', value.toString()];
  return ['boolean', value];
}
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-collections-'));
try {
  let runner = 'import Examples.Shallow.collections\nimport Ariadne.Observe\nopen Ariadne\n';
  const expected = [];
  let count = 0;
  for (const [name, inputs] of Object.entries(cases)) {
    for (const args of inputs) {
      const before = structuredClone(args);
      const result = native[name](...args);
      assert.deepEqual(args, before, `${name} must preserve readonly inputs`);
      const call = `(Extracted_collections.Shallow.${name} ${args.map(argument).join(' ')})`;
      const output = outputs[name] ?? [typeof result === 'boolean' ? 'boolean' : typeof result];
      let shallow;
      if (output[0] === 'array') shallow = `(.ref 0, { heap := [.array (${call}.map Value.${output[1]})] })`;
      else if (output[0] === 'map') {
        const entries = output[1] === 'number' ? `(Ariadne.Shallow.NumberMap.entries ${call})` : `${call}.entries`;
        shallow = `(.ref 0, { heap := [.map (${entries}.map (fun (k, v) => (Value.${output[1]} k, Value.${output[2]} v)))] })`;
      } else if (output[0] === 'option') shallow = `((${call}.map Value.${output[1]}).getD .undefined, {})`;
      else shallow = `(Value.${output[0]} ${call}, {})`;
      runner += `#eval IO.println ((observeResult (.ok ${shallow})).compress)\n`;
      expected.push({ ok: observe(result) });
      const heap = [];
      const preserved = [];
      const encoded = args.map(arg => {
        if (Array.isArray(arg)) {
          const ref = `.ref ${heap.length}`;
          preserved.push([ref, observe(arg)]);
          heap.push(`.array [${arg.map(scalar)}]`);
          return ref;
        }
        if (arg instanceof Map) {
          const ref = `.ref ${heap.length}`;
          preserved.push([ref, observe(arg)]);
          heap.push(`.map [${[...arg].map(([k, v]) => `(${scalar(k)}, ${scalar(v)})`)}]`);
          return ref;
        }
        return scalar(arg);
      });
      runner += `def result${count} := Ariadne.apply Extracted_collections.program 3000 { heap := [${heap}] } (.function "${name}") [${encoded}]\n`;
      runner += `#eval IO.println ((observeResult result${count}).compress)\n`;
      expected.push({ ok: observe(result) });
      for (const [ref, original] of preserved) {
        runner += `#eval IO.println ((observeResult (result${count}.map (fun (_, state) => (${ref}, state)))).compress)\n`;
        expected.push({ ok: original });
      }
      count++;
    }
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').map(JSON.parse), expected);
  console.log(`Shallow collections passed: ${count} three-way comparisons with readonly heap preservation.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
