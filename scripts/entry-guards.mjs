import assert from 'node:assert/strict';
import { mkdir, mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import * as guarded from '../Examples/Shallow/entryguards.runtime.ts';

const rejected = (run, values) => {
  const before = structuredClone(values);
  assert.throws(run, TypeError);
  assert.deepEqual(values, before, 'overlap must throw before the implementation mutates inputs');
};
let count = 0;
const items = [1n];
rejected(() => guarded.flat(items, items), items); count++;
rejected(() => guarded.grow([items], items), items); count++;
const rows = [items];
rejected(() => guarded.outer(rows, items), rows); count++;
const mapped = new Map([['x', items]]);
rejected(() => guarded.mapped(mapped, items), mapped); count++;
const box = new guarded.PublicBox();
rejected(() => guarded.exposed(box, box.items), box.items); count++;
const privateBox = new guarded.Box();
assert.throws(() => guarded.encapsulated(privateBox, privateBox), TypeError); count++;
rejected(() => guarded.names(items, items), items); count++;
assert.equal(guarded.observations(items, items), 5n); count++;
for (const run of [
  () => guarded.grow([[]], items),
  () => guarded.outer([], items),
  () => guarded.mapped(new Map([['x', []]]), items),
  () => guarded.flat(items, []),
  () => guarded.exposed(new guarded.PublicBox(), items),
  () => guarded.encapsulated(new guarded.Box(), new guarded.Box()),
  () => guarded.names(items, []),
]) { run(); count++; }
const runtime = await readFile('Examples/Shallow/entryguards.runtime.ts', 'utf8');
assert.ok(runtime.includes('function __ariadne1_contains'), 'generated helper must avoid source bindings');
const encapsulated = runtime.slice(runtime.indexOf('export function encapsulated'),
  runtime.indexOf('function __ariadne1_encapsulated'));
assert.ok(!encapsulated.includes('__ariadne1_contains'), 'encapsulated classes use root checks');

await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/entry-guards-'));
try {
  const runner = resolve(dir, 'Guards.lean');
  await writeFile(runner, `import Examples.Shallow.entryguards
open Ariadne
open Extracted_entryguards.Shallow
example : flat.entrySafe [.array []] [.ref 0, .ref 0] = false := by kernel_rfl
example : grow.entrySafe [.array [.ref 1], .array []] [.ref 0, .ref 1] = false := by kernel_rfl
example : outer.entrySafe [.array [.ref 1], .array []] [.ref 0, .ref 1] = false := by kernel_rfl
example : mapped.entrySafe [.map [(.string [120], .ref 1)], .array []] [.ref 0, .ref 1] = false := by kernel_rfl
example : exposed.entrySafe [.instance_ "PublicBox" [("items", .ref 1)], .array []] [.ref 0, .ref 1] = false := by kernel_rfl
example : encapsulated.entrySafe [.instance_ "Box" [("items", .ref 1)], .array []] [.ref 0, .ref 0] = false := by kernel_rfl
example : observations.entrySafe [.array []] [.ref 0, .ref 0] = true := by kernel_rfl
example : grow.entrySafe [.array [.ref 1], .array [], .array []] [.ref 0, .ref 2] = true := by kernel_rfl
example : flat.wrapper 100 {heap := [.array []]} [.ref 0, .ref 0] = .error (.typeError "overlapping borrowed arguments") := by kernel_rfl
example : grow.wrapper 100 {heap := [.array [.ref 1], .array []]} [.ref 0, .ref 1] = .error (.typeError "overlapping borrowed arguments") := by kernel_rfl
`);
  const checked = spawnSync('lake', ['env', 'lean', runner], { encoding: 'utf8', timeout: 60000 });
  assert.equal(checked.status, 0, checked.stdout + checked.stderr);
  const original = await readFile('Examples/Tamper/entryguards.lean', 'utf8');
  const tampered = resolve(dir, 'Tampered.lean');
  // Mutate the actual plan, leaving the original program and plan certificate.
  const marker = 'def EntryGuards.«grow».plan';
  const start = original.indexOf(marker);
  assert.ok(start >= 0);
  const end = original.indexOf('\n\n', start);
  const declaration = original.slice(start, end);
  assert.ok(declaration.includes('Traversal.deep'));
  await writeFile(tampered, original.slice(0, start) +
    declaration.replace('Traversal.deep', 'Traversal.root') + original.slice(end));
  const refused = spawnSync('lake', ['env', 'lean', tampered], { encoding: 'utf8', timeout: 60000 });
  assert.notEqual(refused.status, 0, 'a cheaper tampered plan must fail kernel checking');
  assert.ok(refused.stdout.includes('EntryGuards.grow.planned') || refused.stdout.includes('kernel'), refused.stdout);
} finally {
  await rm(dir, { recursive: true, force: true });
}
console.log(`Entry guards passed: ${count} native cases, 10 kernel alias checks, and plan-tampering rejection.`);
