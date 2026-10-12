import { mkdir, mkdtemp, writeFile, readFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/optionals.ts';

const optionalInputs = [[], [undefined], [3], [undefined, 3]];
const maps = [new Map(), new Map([[1n, undefined]]), new Map([[1n, 3]])];
const cases = {
  missing: optionalInputs.map(xs => [xs]),
  present: optionalInputs.map(xs => [xs]),
  fallback: optionalInputs.map(xs => [xs, 7]),
  foundMissing: optionalInputs.map(xs => [xs]),
  mapMissing: maps.flatMap(m => [[m, 1n], [m, 2n]]),
  mapFallback: maps.flatMap(m => [[m, 1n, 8], [m, 2n, 8]]),
  unitMissing: [[[]], [[undefined]], [[undefined, undefined]]],
  nestedMissing: [[undefined], [0], [3]],
  recordMissing: [[{}], [{ value: undefined }], [{ value: 3 }]],
  retainedCoercion: [[0], [9007199254740991]],
  retainedLeft: [[0, undefined], [0, 3], [9007199254740991, undefined]],
  retainedRight: [[undefined, 0], [3, 0], [undefined, 9007199254740991]],
  retainedUnits: [[0], [9007199254740991]],
  literalPresent: [[{ xs: [] }], [{ xs: ['ok'] }], [{ xs: ['ok', 'ok'] }]],
  tagPresent: [[{}], [{ kind: undefined }], [{ kind: 'ok' }]],
  unitField: [[{}], [{ value: undefined }]],
};
const optionalArg = (name, position) => name === 'nestedMissing' ||
  (name === 'retainedLeft' && position === 1) || (name === 'retainedRight' && position === 0);
const units = value => `[${Array.from({ length: value.length }, (_, i) => value.charCodeAt(i)).join(', ')}]`;
const optional = value => value === undefined ? 'none' : `(some (${value} : Int))`;
function nativeArgument(name, position, value) {
  if (Array.isArray(value)) return `[${value.map(x => name === 'unitMissing' ? '()' : optional(x)).join(', ')}]`;
  if (value instanceof Map) return [...value].reduce((m, [k, v]) => `(${m}.set (${k} : Int) ${optional(v)})`, '(JSMap.empty : JSMap Int (Option Int))');
  if (name === 'literalPresent') return `(Extracted_optionals.Shallow.NativeRepresentations.«LiteralContainer».construct ([${value.xs.map(x => `(${units(x)} : JSString)`).join(', ')}], ()))`;
  if (name === 'tagPresent') return `(Extracted_optionals.Shallow.NativeRepresentations.«OptionalTag».construct (${value.kind === undefined ? 'none' : `(some (${units(value.kind)} : JSString))`}, ()))`;
  if (name === 'unitField') return `(Extracted_optionals.Shallow.NativeRepresentations.«UndefinedRecord».construct ((), ()))`;
  if (typeof value === 'object') return `(Extracted_optionals.Shallow.NativeRepresentations.«OptionalRecord».construct (${optional(value.value)}, ()))`;
  if (optionalArg(name, position)) return optional(value);
  return `(${value} : Int)`;
}
const bits = value => {
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, value);
  return view.getBigUint64(0).toString();
};
function observe(value) {
  if (value === undefined) return ['undefined'];
  if (typeof value === 'boolean') return ['boolean', value];
  return ['number', bits(value)];
}
function sourceArgument(value, heap) {
  if (value === undefined) return 'Value.undefined';
  if (typeof value === 'number') return `(Value.number (Float.Model.ofBits ${bits(value)}))`;
  if (typeof value === 'string') return `(Value.string ${units(value)})`;
  if (typeof value === 'bigint') return `(Value.bigint (${value} : Int))`;
  let object;
  if (Array.isArray(value)) object = `(.array [${value.map(x => sourceArgument(x, heap)).join(', ')}])`;
  else if (value instanceof Map) object = `(.map [${[...value].map(([k, v]) => `(${sourceArgument(k, heap)}, ${sourceArgument(v, heap)})`).join(', ')}])`;
  else object = `(.record [${Object.entries(value).map(([k, v]) => `(${JSON.stringify(k)}, ${sourceArgument(v, heap)})`).join(', ')}])`;
  const address = heap.length;
  heap.push(object);
  return `(Value.ref ${address})`;
}
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-optionals-'));
try {
  let runner = 'import Examples.Shallow.optionals\nimport Ariadne.Observe\nopen Ariadne Ariadne.Shallow\n';
  const expected = [];
  let count = 0;
  for (const [name, inputs] of Object.entries(cases)) {
    for (const args of inputs) {
      const before = structuredClone(args);
      const result = native[name](...args);
      assert.deepEqual(args, before, `${name} must preserve borrowed inputs`);
      const nativeArgs = args.map((arg, i) => nativeArgument(name, i, arg)).join(' ');
      const call = `(Extracted_optionals.Shallow.«${name}» ${nativeArgs})`;
      const value = name === 'retainedCoercion' ? `(${call}.map (fun x => Value.number (Float.Model.ofInt x))).getD Value.undefined` :
        typeof result === 'boolean' ? `(Value.boolean ${call})` : `(Value.number (Float.Model.ofInt ${call}))`;
      runner += `#eval IO.println ((observeResult (.ok (${value}, {}))).compress)\n`;
      const heap = [];
      const encoded = args.map(arg => sourceArgument(arg, heap));
      runner += `#eval IO.println ((observeResult (Ariadne.apply Extracted_optionals.program 1000 { heap := [${heap.join(', ')}] } (.function "${name}") [${encoded.join(', ')}])).compress)\n`;
      runner += `#eval IO.println (toString (decide (Extracted_optionals.Shallow.«${name}».safe ${nativeArgs})))\n`;
      const safe = !(name.startsWith('retained') && args.includes(9007199254740991));
      expected.push({ ok: observe(result) }, { ok: observe(result) }, safe);
      count++;
    }
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').map(JSON.parse), expected);
  const edge = resolve(dir, 'EmptyView.ts');
  const candidate = resolve(dir, 'Refused.lean');
  await writeFile(edge, 'type Empty = {}; type Container = { xs: readonly Empty[] }; export function present(value: Container): boolean { return value.xs[0] !== undefined; }');
  await writeFile(candidate, 'preserve existing output');
  const refused = spawnSync('.lake/build/bin/ariadne', ['extract', edge, '--out', candidate], { encoding: 'utf8', timeout: 30000 });
  assert.notEqual(refused.status, 0, refused.stdout + refused.stderr);
  assert.ok((refused.stdout + refused.stderr).includes('A5102'));
  assert.equal(await readFile(candidate, 'utf8'), 'preserve existing output');
  console.log(`Shallow optionals passed: ${count} three-way comparisons, borrowed input preservation and retained safety guards.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
