import assert from 'node:assert/strict';
import { mkdir, mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import * as native from '../Examples/Shallow/projections.runtime.ts';

const cases = {
  incrementElement: [[[0, 5], 0], [[-0], -0], [[Infinity], 0], [[NaN], 0]],
  appendGroup: [[new Map([['x', []]]), 'x', 1n], [new Map([['a', [2n]], ['b', []]]), 'a', -3n],
    [new Map([['\ud800', [0n]]]), '\ud800', 4n]],
  appendRow: [[[[], [2n]], 0, 1n], [[[3n], []], 1, -2n], [[[1n]], -0, 9n]],
  increment: [[[{count: 0}, {count: 4}], 0], [[{count: -0}], -0], [[{count: Infinity}], 0],
    [[{count: NaN}], 0], [[{count: Number.MAX_VALUE}], 0]],
  addCount: [[[{count: 1}, {count: 9}], 1, -3], [[{count: -0}], 0, -0], [[{count: Infinity}], 0, -Infinity]],
  setCount: [[new Map([['x', {count: 1}], ['y', {count: 2}]]), 'x', 7],
    [new Map([['x', {count: 0}]]), 'x', NaN]],
};
const bits = n => { const view = new DataView(new ArrayBuffer(8)); view.setFloat64(0, Number.isNaN(n) ? NaN : n); return view.getBigUint64(0).toString(); };
const units = s => Array.from({length: s.length}, (_, i) => s.charCodeAt(i));
const argument = x => {
  if (typeof x === 'bigint') return `(${x} : Int)`;
  if (typeof x === 'number') return `(Float.Model.ofBits ${bits(x)})`;
  if (typeof x === 'string') return `([${units(x)}] : JSString)`;
  if (Array.isArray(x)) return `[${x.map(argument)}]`;
  if (x instanceof Map) return [...x].reduce((out, [k, v]) => `(Ariadne.Shallow.JSMap.set ${out} ${argument(k)} ${argument(v)})`, 'Ariadne.Shallow.JSMap.empty');
  return `(Extracted_projections.Shallow.NativeTypes.Row.mk ${argument(x.count)})`;
};
const observe = x => {
  if (typeof x === 'bigint') return ['bigint', x.toString()];
  if (typeof x === 'number') return ['number', bits(x)];
  if (typeof x === 'string') return ['string', units(x)];
  if (Array.isArray(x)) return ['array', x.map(observe)];
  if (x instanceof Map) return ['map', [...x].map(([k, v]) => [observe(k), observe(v)])];
  return ['record', [['count', observe(x.count)]]];
};
// Encode nested native values into an independent heap for observation.
const nativeState = (name, expr) => {
  if (name === 'incrementElement') return `(.ref 0, {heap := [.array (${expr}.map Value.number)]})`;
  if (name === 'appendGroup') return `(.ref 0, {heap := [.map (${expr}.entries.zipIdx.map (fun ((k, _), i) => (Value.string k, Value.ref (i+1))))] ++ ${expr}.entries.map (fun (_, xs) => Object.array (xs.map Value.bigint))})`;
  if (name === 'setCount') return `(.ref 0, {heap := [.map (${expr}.entries.zipIdx.map (fun ((k, _), i) => (Value.string k, Value.ref (i+1))))] ++ ${expr}.entries.map (fun (_, row) => Object.record [("count", Value.number row.count)])})`;
  const contents = name === 'appendRow' ? 'Object.array (row.map Value.bigint)' : 'Object.record [("count", Value.number row.count)]';
  return `(.ref 0, {heap := [.array (${expr}.zipIdx.map (fun (_, i) => Value.ref (i+1)))] ++ ${expr}.map (fun row => ${contents})})`;
};
await mkdir('work', {recursive: true});
const dir = await mkdtemp(resolve('work/shallow-projections-'));
try {
  let runner = 'import Examples.Shallow.projections\nimport Ariadne.Observe\nopen Ariadne\n' +
    '#check @Extracted_projections.Shallow.appendGroup_source\n' +
    '#check @Extracted_projections.Shallow.SourceProjectionChecks.appendGroup.wrapperSource\n' +
    '#check @Extracted_projections.Shallow.appendRow_source\n' +
    '#check @Extracted_projections.Shallow.SourceProjectionChecks.appendRow.wrapperSource\n' +
    '#check @Extracted_projections.Shallow.increment_source\n' +
    '#check @Extracted_projections.Shallow.SourceProjectionChecks.increment.wrapperSource\n';
  const expected = [];
  let count = 0;
  for (const [name, entries] of Object.entries(cases)) for (const input of entries) {
    const before = structuredClone(input);
    const args = structuredClone(input);
    // Runtime projection must retain the identity of the selected element.
    const selected = args[0] instanceof Map ? args[0].get(args[1]) : args[0][args[1]];
    native[name](...args);
    if (typeof selected === 'object') assert.equal(args[0] instanceof Map ? args[0].get(args[1]) : args[0][args[1]], selected);
    const heap = [];
    const encode = x => {
      if (typeof x !== 'object') return `(Value.${typeof x === 'bigint' ? 'bigint' : typeof x} ${argument(x)})`;
      const address = heap.length; heap.push(null);
      heap[address] = Array.isArray(x) ? `.array [${x.map(encode)}]` : x instanceof Map ?
        `.map [${[...x].map(([k, v]) => `(${encode(k)}, ${encode(v)})`)}]` : `.record [("count", ${encode(x.count)})]`;
      return `.ref ${address}`;
    };
    const encoded = before.map(encode);
    runner += `def native${count} := Extracted_projections.Shallow.${name} ${before.map(argument).join(' ')}\n`;
    runner += `example : Extracted_projections.Shallow.${name}.safe ${before.map(argument).join(' ')} := by decide\n`;
    runner += `def model${count} := Ariadne.apply Extracted_projections.program 500 {heap := [${heap}]} (.function "${name}") [${encoded}]\n`;
    runner += `#eval IO.println ((observeResult (.ok ${nativeState(name, `(native${count}.2.1)`)})).compress)\n`;
    runner += `#eval IO.println ((observeResult (model${count}.map (fun (_, state) => (${encoded[0]}, state)))).compress)\n`;
    expected.push({ok: observe(args[0])}, {ok: observe(args[0])});
    count++;
  }
  for (const index of [-1, 0.5, 1, Infinity, NaN]) {
    assert.throws(() => native.increment([{count: 0}], index), TypeError);
    runner += `example : ¬ Extracted_projections.Shallow.increment.safe [⟨Float.Model.ofBits 0⟩] ${argument(index)} := by decide\n`;
  }
  assert.throws(() => native.appendGroup(new Map(), 'missing', 1n), TypeError);
  runner += 'example : ¬ Extracted_projections.Shallow.appendGroup.safe Ariadne.Shallow.JSMap.empty [109] 1 := by decide\n';
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], {encoding: 'utf8', timeout: 120000, maxBuffer: 8e6});
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').filter(line => line.startsWith('{')).map(JSON.parse), expected);
  for (const [fixture, name] of [['projections', 'appendGroup'], ['projectionarray', 'appendRow'], ['projectionfield', 'increment']]) {
    const original = await readFile(`Examples/Tamper/${fixture}.lean`, 'utf8');
    const start = original.indexOf(`theorem «${name}_source»`);
    assert.ok(start >= 0, 'the universal stateful source witness must be emitted');
    const end = original.indexOf(`theorem SourceProjectionChecks.«${name}».wrapperSource`, start);
    assert.ok(end > start);
    const declaration = original.slice(start, end);
    const updated = declaration.match(name === 'increment' ? /  let replacement :[^\n]+/ : /  have updated :[^\n]+/)[0];
    const alteredUpdates = name === 'increment' ? updated.replace('old.«count» + delta', 'old.«count»') :
      updated.replace('old ++ [«_value#arg»]', 'old');
    assert.notEqual(updated, alteredUpdates);
    const alterations = [
      declaration.replace(updated, alteredUpdates),
      declaration.replace(new RegExp(`\\(_sourceSafe : «${name}»\\.safe[^\\n]+\\)`), '(_sourceSafe : True)'),
      declaration.replace(`source "${name}"`, 'source "forgedEntry"'),
    ];
    for (const [i, altered] of alterations.entries()) {
      assert.notEqual(altered, declaration);
      const tampered = resolve(dir, `Tampered${name}${i}.lean`);
      await writeFile(tampered, original.slice(0, start) + altered + original.slice(end));
      const refused = spawnSync('lake', ['env', 'lean', tampered], {encoding: 'utf8', timeout: 60000, maxBuffer: 8e6});
      assert.notEqual(refused.status, 0, 'a forged source mutation witness must fail kernel checking');
      assert.ok(refused.stdout.includes('error'), refused.stdout + refused.stderr);
    }
  }
  console.log(`Shallow projections passed: ${count} three-way heap comparisons, retained element identities, 6 missing-element guards, 6 universal source witnesses, and 9 small-fixture tamper checks.`);
} finally { await rm(dir, {recursive: true, force: true}); }
