import { mkdir, mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/records.ts';

const p = { x: 3n, label: 'a', weight: 2n };
const q = { label: '\ud800', x: -1n };
const cases = {
  make: [[0n, ''], [10n ** 40n, '\0\ud800']],
  sum: [[[]], [[p, q]], [[{ x: 9n, label: '', weight: undefined }]]],
  find: [[[], 0n], [[p, q], 0n], [[p, q], -2n], [[p], 9n]],
  relabel: [[p, 'b'], [q, '\0']], tagged: [[0n], [-5n]],
  tagName: [[{ kind: 'ok', payload: 7n }]],
  weird: [[1n], [10n ** 40n]],
  fields: [[{ length: 3n, size: 'hello', rec: 8n }]],
  duplicate: [[]], empty: [[]],
};
const inputs = {
  sum: ['Point[]'], find: ['Point[]', 'bigint'], relabel: ['Point', 'string'],
  tagName: ['Tagged'], fields: ['Weird'],
};
const outputs = { make: 'Point', find: 'Point?', relabel: 'Point', tagged: 'Tagged', weird: 'Weird', duplicate: 'Point', empty: 'Empty' };
const fields = { Point: ['x', 'label', 'weight'], Tagged: ['kind', 'payload'], Weird: ['length', 'size', 'rec'], Empty: [] };
const units = s => Array.from({ length: s.length }, (_, i) => s.charCodeAt(i));
function scalar(value) {
  if (value === undefined) return '.undefined';
  if (typeof value === 'string') return `(Value.string [${units(value)}])`;
  return `(Value.bigint (${value}))`;
}
function argument(value, type) {
  if (type === 'Point[]') return `[${value.map(x => argument(x, 'Point'))}]`;
  if (type === 'Point') return `(NativeTypes.Point.mk (${value.x}) [${units(value.label)}] ${value.weight === undefined ? 'none' : `(some (${value.weight}))`})`;
  if (type === 'Tagged') return `(NativeTypes.Tagged.mk (${value.payload}))`;
  if (type === 'Weird') return `(NativeTypes.Weird.mk (${value.length}) [${units(value.size)}] (${value.rec}))`;
  if (typeof value === 'string') return `([${units(value)}] : JSString)`;
  return `(${value} : Int)`;
}
function observe(value) {
  if (value === undefined) return ['undefined'];
  if (typeof value === 'string') return ['string', units(value)];
  if (typeof value === 'bigint') return ['bigint', value.toString()];
  if (Array.isArray(value)) return ['array', value.map(observe)];
  return ['record', Object.entries(value).map(([k, v]) => [k, observe(v)])];
}
// Named records are observed through their declared fields. An optional field
// reads as undefined whether absent or explicitly present; property enumeration
// and own-property tests are outside the admitted source language.
function typedObservation(value, type) {
  if (value === undefined || !type) return observe(value);
  const name = type.replace('?', '');
  return ['record', fields[name].map(key => [key, observe(value[key])])];
}
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-records-'));
try {
  let runner = `import Examples.Shallow.records
import Ariadne.Observe
open Ariadne Extracted_records.Shallow
def pointValue (p : NativeTypes.Point) : Value × State :=
  (.ref 0, { heap := [.record [("x", .bigint p.x), ("label", .string p.label),
    ("weight", (p.weight.map Value.bigint).getD .undefined)]] })
def taggedValue (p : NativeTypes.Tagged) : Value × State :=
  (.ref 0, { heap := [.record [("kind", .string [111, 107]), ("payload", .bigint p.payload)]] })
def weirdValue (p : NativeTypes.Weird) : Value × State :=
  (.ref 0, { heap := [.record [("length", .bigint p.length), ("size", .string p.size), ("rec", .bigint p.field2)]] })
def emptyValue (_ : NativeTypes.Empty) : Value × State := (.ref 0, { heap := [.record []] })
def typedRecord (names : List String) (result : Result (Value × State)) : Result (Value × State) :=
  result.map fun (value, state) => match value with
    | .ref loc => match state.heap[loc]? with
      | some (.record properties) =>
        let (fresh, out) := state.alloc (.record (names.map fun name => (name, (properties.lookup name).getD .undefined)))
        (.ref fresh, out)
      | _ => (value, state)
    | _ => (value, state)
`;
  const expected = [];
  let count = 0;
  for (const [name, entries] of Object.entries(cases)) {
    for (const args of entries) {
      const before = structuredClone(args);
      const result = native[name](...args);
      assert.deepEqual(args, before, `${name} must preserve inputs`);
      const call = `(Extracted_records.Shallow.${name} ${args.map((arg, i) => argument(arg, inputs[name]?.[i])).join(' ')})`;
      const type = outputs[name];
      let encoded;
      if (type === 'Point?') encoded = `((${call}.map pointValue).getD (.undefined, {}))`;
      else if (type) encoded = `(${type[0].toLowerCase() + type.slice(1)}Value ${call})`;
      else encoded = `(Value.${typeof result === 'string' ? 'string' : 'bigint'} ${call}, {})`;
      runner += `#eval IO.println ((observeResult (.ok ${encoded})).compress)\n`;
      expected.push({ ok: typedObservation(result, type) });
      const heap = [];
      const encode = value => {
        if (value === undefined || typeof value !== 'object') return scalar(value);
        const slot = heap.length;
        heap.push(null);
        heap[slot] = Array.isArray(value) ? `.array [${value.map(encode)}]` :
          `.record [${Object.entries(value).map(([k, v]) => `(${JSON.stringify(k)}, ${encode(v)})`)}]`;
        return `.ref ${slot}`;
      };
      const modelArgs = args.map(encode);
      runner += `def result${count} := Ariadne.apply Extracted_records.program 3000 { heap := [${heap}] } (.function "${name}") [${modelArgs}]\n`;
      const model = type ? `(typedRecord [${fields[type.replace('?', '')].map(x => JSON.stringify(x))}] result${count})` : `result${count}`;
      runner += `#eval IO.println ((observeResult ${model}).compress)\n`;
      expected.push({ ok: typedObservation(result, type) });
      for (const [i, arg] of args.entries()) {
        if (arg === undefined || typeof arg !== 'object') continue;
        runner += `#eval IO.println ((observeResult (result${count}.map (fun (_, state) => (${modelArgs[i]}, state)))).compress)\n`;
        expected.push({ ok: observe(arg) });
      }
      count++;
    }
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').map(JSON.parse), expected);
  const generated = await readFile('Examples/Shallow/records.lean', 'utf8');
  const start = generated.indexOf('structure NativeTypes.«Point»');
  const stop = generated.indexOf('structure NativeTypes.«Tagged»');
  assert.ok(start >= 0 && stop > start);
  const representation = generated.slice(start, stop);
  const broken = representation.replace('_value.«x»', '(_value.«x» + 1)');
  assert.notEqual(broken, representation);
  const tamperPath = resolve(dir, 'Tamper.lean');
  await writeFile(tamperPath, `import Ariadne.Shallow.Named\nopen Ariadne.Shallow\n${broken}`);
  const rejected = spawnSync('lake', ['env', 'lean', tamperPath], { encoding: 'utf8', timeout: 120000 });
  assert.notEqual(rejected.status, 0, 'a non-inverse named representation must fail kernel checking');
  assert.match(rejected.stdout, /Tactic `rfl` failed/);
  console.log(`Shallow records passed: ${count} three-way typed-field comparisons, input heap preservation, and representation tamper rejection.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
