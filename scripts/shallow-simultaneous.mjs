import assert from 'node:assert/strict';
import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import * as native from '../Examples/Shallow/simultaneous.runtime.ts';

const row = count => ({count});
const cases = {
  swapRows: [[[row(1n), row(2n), row(3n)], 0, 2], [[row(4n), row(-5n)], 1, -0]],
  swapGroups: [[new Map([['a', row(1n)], ['b', row(2n)]]), 'a', 'b'],
    [new Map([['\ud800', row(3n)], ['', row(-4n)]]), '', '\ud800']],
  swapNumbers: [[new Map([[NaN, row(1n)], [0, row(2n)]]), NaN, -0],
    [new Map([[Infinity, row(3n)], [-Infinity, row(4n)]]), Infinity, -Infinity],
    [new Map([[0.5, row(5n)], [1.5, row(6n)]]), 1.5, 0.5]],
  appendRows: [[[[], [], [9n]], 0, 1], [[[3n], [4n]], 1, 0], [[[], [5n]], -0, 1]],
};
const failures = [
  ['swapRows', [[row(1n)], 0, -0]],
  ['swapGroups', [new Map([['x', row(1n)]]), 'x', 'x']],
  ['swapNumbers', [new Map([[NaN, row(1n)]]), NaN, NaN]],
  ['swapNumbers', [new Map([[0, row(1n)]]), -0, 0]],
  ['swapNumbers', [new Map([[Infinity, row(1n)]]), Infinity, Infinity]],
  ['appendRows', [[[5n]], 0, 0]],
];
const bits = number => {
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, Number.isNaN(number) ? NaN : number);
  return view.getBigUint64(0).toString();
};
const units = string => Array.from({length: string.length}, (_, i) => string.charCodeAt(i));
const argument = (value, numeric = false) => {
  if (typeof value === 'bigint') return `(${value} : Int)`;
  if (typeof value === 'number') return `(Float.Model.ofBits ${bits(value)})`;
  if (typeof value === 'string') return `([${units(value)}] : JSString)`;
  if (Array.isArray(value)) return `[${value.map(x => argument(x, numeric))}]`;
  if (value instanceof Map) {
    const namespace = numeric ? 'NumberMap' : 'JSMap';
    return [...value].reduce((out, [key, item]) =>
      `(Ariadne.Shallow.${namespace}.set ${out} ${argument(key)} ${argument(item)})`,
      `Ariadne.Shallow.${namespace}.empty`);
  }
  return `(Extracted_simultaneous.Shallow.NativeTypes.Row.mk ${argument(value.count)})`;
};
const observe = value => {
  if (typeof value === 'bigint') return ['bigint', value.toString()];
  if (typeof value === 'number') return ['number', bits(value)];
  if (typeof value === 'string') return ['string', units(value)];
  if (Array.isArray(value)) return ['array', value.map(observe)];
  if (value instanceof Map) return ['map', [...value].map(([key, item]) => [observe(key), observe(item)])];
  return ['record', [['count', observe(value.count)]]];
};
const encodeArgs = args => {
  const heap = [];
  const encode = value => {
    if (typeof value !== 'object') return `(Value.${typeof value === 'bigint' ? 'bigint' : typeof value} ${argument(value)})`;
    const address = heap.length;
    heap.push(null);
    heap[address] = Array.isArray(value) ? `.array [${value.map(encode)}]` : value instanceof Map ?
      `.map [${[...value].map(([key, item]) => `(${encode(key)}, ${encode(item)})`)}]` :
      `.record [("count", ${encode(value.count)})]`;
    return `.ref ${address}`;
  };
  return {encoded: args.map(encode), heap};
};
const nativeState = (name, expr) => {
  if (name.startsWith('swap') && name !== 'swapRows') {
    const key = name === 'swapNumbers' ? 'Value.number' : 'Value.string';
    return `(.ref 0, {heap := [.map (${expr}.entries.zipIdx.map (fun ((k, _), i) => (${key} k, Value.ref (i+1))))] ++ ${expr}.entries.map (fun (_, item) => Object.record [("count", Value.bigint item.count)])})`;
  }
  const child = name === 'appendRows' ? 'Object.array (item.map Value.bigint)' :
    'Object.record [("count", Value.bigint item.count)]';
  return `(.ref 0, {heap := [.array (${expr}.zipIdx.map (fun (_, i) => Value.ref (i+1)))] ++ ${expr}.map (fun item => ${child})})`;
};
await mkdir('work', {recursive: true});
const dir = await mkdtemp(resolve('work/shallow-simultaneous-'));
try {
  let runner = 'import Examples.Shallow.simultaneous\nimport Ariadne.Observe\n' +
    'import Ariadne.Shallow.Adequacy.ProjectionGuard\nopen Ariadne Ariadne.Shallow\n' +
    '#check @Adequacy.array_projection_guard\n#check @Adequacy.map_projection_guard\n' +
    '#check @Ownership.checkArgument_projection_iff\n';
  const expected = [];
  let count = 0;
  for (const [name, entries] of Object.entries(cases)) for (const input of entries) {
    const args = structuredClone(input);
    const get = key => args[0] instanceof Map ? args[0].get(key) : args[0][key];
    const selected = [get(args[1]), get(args[2])];
    native[name](...args);
    assert.equal(get(args[1]), selected[0]);
    assert.equal(get(args[2]), selected[1]);
    const {encoded, heap} = encodeArgs(input);
    const nativeArgs = input.map(x => argument(x, name === 'swapNumbers')).join(' ');
    runner += `def native${count} := Extracted_simultaneous.Shallow.${name} ${nativeArgs}\n`;
    runner += `example : Extracted_simultaneous.Shallow.${name}.safe ${nativeArgs} := by decide\n`;
    runner += `def model${count} := Extracted_simultaneous.Shallow.${name}.wrapper 500 {heap := [${heap}]} [${encoded}]\n`;
    runner += `#eval IO.println ((observeResult (.ok ${nativeState(name, `(native${count}.2.1)`)})).compress)\n`;
    runner += `#eval IO.println ((observeResult (model${count}.map (fun (_, state) => (.ref 0, state)))).compress)\n`;
    expected.push({ok: observe(args[0])}, {ok: observe(args[0])});
    count++;
  }
  for (const [name, args] of failures) {
    const before = observe(args[0]);
    assert.throws(() => native[name](...args), error => error instanceof TypeError && error.message === 'overlapping projected arguments');
    assert.deepEqual(observe(args[0]), before, 'the guard must fail before any mutation');
    const {encoded, heap} = encodeArgs(args);
    runner += `example : ¬ Extracted_simultaneous.Shallow.${name}.safe ${args.map(x => argument(x, name === 'swapNumbers')).join(' ')} := by decide\n`;
    runner += `#eval IO.println ((observeResult (Extracted_simultaneous.Shallow.${name}.wrapper 500 {heap := [${heap}]} [${encoded}])).compress)\n`;
    expected.push({error: 'Ariadne.Fault.typeError "overlapping projected arguments"'});
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], {encoding: 'utf8', timeout: 120000, maxBuffer: 8e6});
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').filter(line => line.startsWith('{')).map(JSON.parse), expected);
  console.log(`Simultaneous projections passed: ${count} three-way heap comparisons, retained selected identities, 6 guards that throw before mutation, and universal footprint separation proofs.`);
} finally { await rm(dir, {recursive: true, force: true}); }
