import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/state.ts';

const empty = () => new Map();
const one = () => new Map([['a', 4n]]);
const cases = {
  bump: [[empty(), 'a'], [one(), 'a'], [one(), '\ud800']],
  count: [[empty(), []], [one(), ['a', 'b', 'a']], [empty(), ['\0', '\ud800', '\0']]],
  transfer: [[empty(), empty(), 'a'], [one(), empty(), 'a'], [one(), new Map([['a', 9n], ['b', 2n]]), 'a']],
  scoped: [[empty()], [one()]], early: [[one(), true], [one(), false]],
  read: [[empty(), 'a'], [one(), 'a']], twice: [[empty(), 'a'], [one(), 'a']],
  localCalls: [['a'], ['\ud800']], swapInto: [[one(), empty(), 'a'], [empty(), one(), 'a']],
  fromFresh: [['a'], ['\0']], append: [[[], []], [[1n], [2n, 3n]]],
  appendLength: [[[], [1n, 2n]], [[9n], []]],
  addAll: [[new Set(), []], [new Set([1n]), [2n, 1n, 3n]]],
  until: [[empty(), [], 'stop'], [one(), ['a', 'stop', 'b'], 'stop'], [empty(), ['a', 'a'], 'stop']],
  pureCopy: [[[]], [[1n, 2n]]], copyCaller: [[[]], [[1n, 2n]]],
};
const mutated = { bump: [0], count: [0], transfer: [0, 1], scoped: [0], early: [0], twice: [0],
  swapInto: [0, 1], append: [0], appendLength: [0], addAll: [0], until: [0] };
const units = s => Array.from({ length: s.length }, (_, i) => s.charCodeAt(i));
const bits = n => { const view = new DataView(new ArrayBuffer(8)); view.setFloat64(0, n); return view.getBigUint64(0).toString(); };
function argument(value) {
  if (typeof value === 'string') return `([${units(value)}] : JSString)`;
  if (typeof value === 'bigint') return `(${value} : Int)`;
  if (typeof value === 'boolean') return String(value);
  if (Array.isArray(value)) return `[${value.map(argument)}]`;
  if (value instanceof Map) return [...value].reduce((out, [k, v]) =>
    `(Ariadne.Shallow.JSMap.set ${out} ${argument(k)} ${argument(v)})`,
    '(Ariadne.Shallow.JSMap.empty : Ariadne.Shallow.JSMap JSString Int)');
  if (value instanceof Set) return [...value].reduce((out, v) => `(Ariadne.Shallow.JSSet.add ${out} ${argument(v)})`,
    '(Ariadne.Shallow.JSSet.empty : Ariadne.Shallow.JSSet Int)');
  throw new Error('unsupported input');
}
function observe(value) {
  if (value === undefined) return ['undefined'];
  if (typeof value === 'bigint') return ['bigint', value.toString()];
  if (typeof value === 'string') return ['string', units(value)];
  if (typeof value === 'number') return ['number', bits(value)];
  if (Array.isArray(value)) return ['array', value.map(observe)];
  if (value instanceof Map) return ['map', [...value].map(([k, v]) => [observe(k), observe(v)])];
  if (value instanceof Set) return ['set', [...value].map(observe)];
  return ['boolean', value];
}
function nativeValue(expr, value, arrayType = 'bigint') {
  if (value === undefined) return '(Value.undefined, {})';
  if (Array.isArray(value)) return `(.ref 0, { heap := [.array (${expr}.map Value.${arrayType})] })`;
  if (value instanceof Map) return `(.ref 0, { heap := [.map (${expr}.entries.map (fun (k, v) => (Value.string k, Value.bigint v)))] })`;
  if (value instanceof Set) return `(.ref 0, { heap := [.set (${expr}.values.map Value.bigint)] })`;
  return `(Value.${typeof value} ${expr}, {})`;
}
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-state-'));
try {
  let runner = 'import Examples.Shallow.state\nimport Ariadne.Observe\nopen Ariadne\n';
  let count = 0;
  const expected = [];
  for (const [name, entries] of Object.entries(cases)) for (const input of entries) {
    const before = structuredClone(input);
    const args = structuredClone(input);
    const result = native[name](...args);
    const writes = mutated[name] ?? [];
    runner += `def native${count} := Extracted_state.Shallow.${name} ${before.map(argument).join(' ')}\n`;
    const returned = writes.length ? `native${count}.1` : `native${count}`;
    runner += `#eval IO.println ((observeResult (.ok ${nativeValue(returned, result)})).compress)\n`;
    expected.push({ ok: observe(result) });
    const heap = [];
    const encode = value => {
      if (typeof value !== 'object') return `(Value.${typeof value} ${argument(value)})`;
      const slot = heap.length;
      heap.push(null);
      heap[slot] = value instanceof Map ? `.map [${[...value].map(([k, v]) => `(${encode(k)}, ${encode(v)})`)}]` :
        value instanceof Set ? `.set [${[...value].map(encode)}]` : `.array [${value.map(encode)}]`;
      return `.ref ${slot}`;
    };
    const encoded = before.map(encode);
    runner += `def model${count} := Ariadne.apply Extracted_state.program 5000 { heap := [${heap}] } (.function "${name}") [${encoded}]\n`;
    runner += `#eval IO.println ((observeResult model${count}).compress)\n`;
    expected.push({ ok: observe(result) });
    for (const [i, value] of args.entries()) {
      if (typeof value !== 'object') continue;
      const position = writes.indexOf(i);
      const state = position < 0 ? `(${argument(before[i])})` : `(native${count}${'.2'.repeat(position + 1)}.1)`;
      const arrayType = Array.isArray(value) && (typeof value[0] === 'string' || ['count', 'until'].includes(name)) ? 'string' : 'bigint';
      runner += `#eval IO.println ((observeResult (.ok ${nativeValue(state, value, arrayType)})).compress)\n`;
      runner += `#eval IO.println ((observeResult (model${count}.map (fun (_, state) => (${encoded[i]}, state)))).compress)\n`;
      expected.push({ ok: observe(value) }, { ok: observe(value) });
    }
    count++;
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').map(JSON.parse), expected);
  console.log(`Shallow state passed: ${count} three-way comparisons of returns and caller-visible heaps.`);
} finally { await rm(dir, { recursive: true, force: true }); }
