import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/unions.ts';

const valid = (version, id) => ({ kind: 'valid', version, id });
const rejected = reason => ({ reason, kind: 'rejected' });
const a = valid(2n, 'a'), b = valid(2n, 'b'), c = valid(3n, '\ud800'), bad = rejected('no');
const events = [{ kind: 'created', id: 'a' }, { value: 9n, kind: 'changed' }, { kind: 'deleted', id: '\0' }];
const cases = {
  valid: [[0n, ''], [10n ** 40n, '\0\ud800']], rejected: [[''], ['reason']],
  kind: [[a], [bad]], getVersion: [[a], [bad]], copyIfValid: [[a], [bad]],
  fallback: [[undefined], [a], [bad]], replace: [[a], [bad]],
  filtered: [[[], 0n], [[a, bad, c, b], 2n], [[a, bad, c], 4n]],
  eventValue: events.map(x => [x]), eventTag: events.map(x => [x]), changed: [[0n], [-8n]],
  choose: [[[], 0n], [[bad], 0n], [[a, b, c], 4n], [[a, b], 2n], [[a, a], 2n]],
};
function permutations(xs) {
  if (!xs.length) return [[]];
  return xs.flatMap((x, i) => permutations(xs.filter((_, j) => i !== j)).map(rest => [x, ...rest]));
}
for (const xs of permutations([a, b, c, bad])) cases.choose.push([xs, 2n]);
const schemas = { valid: ['kind', 'version', 'id'], rejected: ['kind', 'reason'],
  created: ['kind', 'id'], changed: ['kind', 'value'], deleted: ['kind', 'id'] };
const units = s => Array.from({ length: s.length }, (_, i) => s.charCodeAt(i));
function argument(value, optional = false) {
  if (optional) return value === undefined ? 'none' : `(some ${argument(value)})`;
  if (Array.isArray(value)) return `[${value.map(x => argument(x))}]`;
  if (typeof value === 'string') return `([${units(value)}] : JSString)`;
  if (typeof value === 'bigint') return `(${value} : Int)`;
  switch (value.kind) {
    case 'valid': return `(NativeTypes.Candidate.valid ⟨${argument(value.version)}, ${argument(value.id)}⟩)`;
    case 'rejected': return `(NativeTypes.Candidate.rejected ⟨${argument(value.reason)}⟩)`;
    case 'created': return `(NativeTypes.Event.created ⟨${argument(value.id)}⟩)`;
    case 'changed': return `(NativeTypes.Event.right (NativeTypes.«Event#right».changed ⟨${argument(value.value)}⟩))`;
    case 'deleted': return `(NativeTypes.Event.right (NativeTypes.«Event#right».deleted ⟨${argument(value.id)}⟩))`;
  }
  throw new Error('unknown union variant');
}
const scalar = value => value === undefined ? 'Value.undefined' :
  `(Value.${typeof value} ${argument(value)})`;
function observe(value, typed = false) {
  if (value === undefined) return ['undefined'];
  if (typeof value === 'bigint') return ['bigint', value.toString()];
  if (typeof value === 'string') return ['string', units(value)];
  if (Array.isArray(value)) return ['array', value.map(x => observe(x, typed))];
  const names = typed ? schemas[value.kind] : Object.keys(value);
  return ['record', names.map(k => [k, observe(value[k], typed)])];
}
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-unions-'));
try {
  let runner = `import Examples.Shallow.unions
import Ariadne.Observe
open Ariadne Extracted_unions.Shallow
def candidateFields : NativeTypes.Candidate → List (String × Value)
  | .valid p => [("kind", .string [118, 97, 108, 105, 100]), ("version", .bigint p.version), ("id", .string p.id)]
  | .rejected p => [("kind", .string [114, 101, 106, 101, 99, 116, 101, 100]), ("reason", .string p.reason)]
def eventFields : NativeTypes.Event → List (String × Value)
  | .created p => [("kind", .string [99, 114, 101, 97, 116, 101, 100]), ("id", .string p.id)]
  | .right (.changed p) => [("kind", .string [99, 104, 97, 110, 103, 101, 100]), ("value", .bigint p.value)]
  | .right (.deleted p) => [("kind", .string [100, 101, 108, 101, 116, 101, 100]), ("id", .string p.id)]
def recordValue (fields : List (String × Value)) : Value × State := (.ref 0, { heap := [.record fields] })
def candidateValue (value : NativeTypes.Candidate) := recordValue (candidateFields value)
def candidateArray (values : List NativeTypes.Candidate) : Value × State :=
  (.ref values.length, { heap := values.map (fun v => Object.record (candidateFields v)) ++
    [.array ((List.range values.length).map Value.ref)] })
def schema (properties : List (String × Value)) : List String :=
  match properties.lookup "kind" with
${Object.entries(schemas).map(([tag, fields]) => `  | some (.string [${units(tag)}]) => [${fields.map(x => JSON.stringify(x))}]`).join('\n')}
  | _ => properties.map Prod.fst
def typedObserve (state : State) : Value → Lean.Json
  | .ref loc => match state.heap[loc]? with
    | some (.record fields) =>
      Lean.Json.arr #[Lean.toJson "record", Lean.Json.arr ((schema fields).map (fun name =>
        Lean.Json.arr #[Lean.toJson name, observe 100 state ((fields.lookup name).getD .undefined)])).toArray]
    | some (.array values) =>
      Lean.Json.arr #[Lean.toJson "array", Lean.Json.arr (values.map fun v =>
        match v with
        | .ref i => match state.heap[i]? with
          | some (.record fields) => Lean.Json.arr #[Lean.toJson "record", Lean.Json.arr ((schema fields).map (fun name =>
              Lean.Json.arr #[Lean.toJson name, observe 100 state ((fields.lookup name).getD .undefined)])).toArray]
          | _ => observe 100 state v
        | _ => observe 100 state v).toArray]
    | _ => observe 100 state (.ref loc)
  | value => observe 100 state value
def typedResult : Result (Value × State) → Lean.Json
  | .ok (value, state) => Lean.Json.mkObj [("ok", typedObserve state value)]
  | error => observeResult error
`;
  const expected = [];
  let count = 0;
  for (const [name, entries] of Object.entries(cases)) {
    for (const args of entries) {
      const before = structuredClone(args);
      const result = native[name](...args);
      assert.deepEqual(args, before);
      const call = `(Extracted_unions.Shallow.${name} ${args.map(x => argument(x, name === 'fallback')).join(' ')})`;
      let shallow;
      if (name === 'getVersion') shallow = `((${call}.map Value.bigint).getD .undefined, {})`;
      else if (['choose', 'copyIfValid'].includes(name)) shallow = `((${call}.map candidateValue).getD (.undefined, {}))`;
      else if (name === 'filtered') shallow = `(candidateArray ${call})`;
      else if (name === 'changed') shallow = `(recordValue (eventFields ${call}))`;
      else if (typeof result === 'object') shallow = `(candidateValue ${call})`;
      else shallow = `(Value.${typeof result} ${call}, {})`;
      runner += `#eval IO.println ((observeResult (.ok ${shallow})).compress)\n`;
      expected.push({ ok: observe(result, true) });
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
      runner += `def result${count} := Ariadne.apply Extracted_unions.program 5000 { heap := [${heap}] } (.function "${name}") [${modelArgs}]\n`;
      runner += `#eval IO.println ((typedResult result${count}).compress)\n`;
      expected.push({ ok: observe(result, true) });
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
  console.log(`Shallow unions passed: ${count} three-way typed-field comparisons with input heap preservation.`);
} finally { await rm(dir, { recursive: true, force: true }); }
