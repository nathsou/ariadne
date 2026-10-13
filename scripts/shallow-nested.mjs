// Nested owned mutation: passing a field of an owned record to a function that
// mutates its parameter lowers to a backward function, whose final state is
// written back into the field. The emitted definitions must agree with the
// TypeScript source and the original evaluator.
import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/nested.ts';

const cases = {
  fill: [[0n], [7n]],
  both: [[-1n], [4n]],
  counted: [[[]], [[1n, 2n, 3n]]],
  partition: [[[]], [[1n, 20n, 3n, 40n, 9n, 10n]]],
};
const records = new Set(['fill', 'both', 'partition']);
const argument = value => Array.isArray(value) ? `[${value.map(argument)}]` : `(${value} : Int)`;
const units = text => [...text].map(c => c.charCodeAt(0));
const observe = value => typeof value === 'bigint' ? ['bigint', value.toString()]
  : typeof value === 'string' ? ['string', units(value)]
  : Array.isArray(value) ? ['array', value.map(observe)]
  : ['record', Object.entries(value).map(([k, v]) => [k, observe(v)])];
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-nested-'));
try {
  let runner = 'import Examples.Shallow.nested\nimport Ariadne.Observe\nopen Ariadne Lean\n';
  runner += 'def bigint (x : Int) : Json := Json.arr #[toJson "bigint", toJson (toString x)]\n';
  runner += 'def array (xs : List Int) : Json := Json.arr #[toJson "array", Json.arr ((xs.map bigint).toArray)]\n';
  runner += 'def string (s : JSString) : Json := Json.arr #[toJson "string", toJson (s.map UInt16.toNat)]\n';
  runner += 'def bag (b : Extracted_nested.Shallow.NativeTypes.«Bag») : Json := Json.arr #[toJson "record", Json.arr #[' +
    'Json.arr #[toJson "items", array b.items], Json.arr #[toJson "extra", array b.extra], Json.arr #[toJson "label", string b.label]]]\n';
  const expected = [];
  for (const [name, inputs] of Object.entries(cases)) {
    for (const args of inputs) {
      const before = structuredClone(args);
      const result = native[name](...args);
      assert.deepEqual(args, before, `${name} must preserve readonly inputs`);
      expected.push(observe(result), { ok: observe(result) });
      const call = `(Extracted_nested.Shallow.${name} ${args.map(argument).join(' ')})`;
      runner += `#eval IO.println (${records.has(name) ? 'bag' : 'bigint'} ${call}).compress\n`;
      const heap = [];
      const encoded = args.map(arg => {
        if (!Array.isArray(arg)) return `(.bigint ${argument(arg)})`;
        heap.push(`.array [${arg.map(x => `Value.bigint ${argument(x)}`)}]`);
        return `.ref ${heap.length - 1}`;
      });
      runner += `#eval IO.println ((observeResult (Ariadne.apply Extracted_nested.program 3000 { heap := [${heap}] } (.function "${name}") [${encoded}])).compress)\n`;
    }
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], { encoding: 'utf8', timeout: 300000, maxBuffer: 8e6 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').map(JSON.parse), expected);
  console.log(`Shallow nested mutation passed: ${expected.length / 2} three-way comparisons with readonly input preservation.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
