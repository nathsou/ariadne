// Generated weakest-precondition source theorems for array and record functions must be
// emitted for the supported fragment and rejected by the kernel when the
// callback specification, the claimed result or the proved function changes.
import assert from 'node:assert/strict';
import { mkdir, mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';

const expected = {
  'Examples/Shallow/arrays.lean': {
    covered: ['transform', 'sum', 'find', 'allPositive', 'anyPositive', 'copy', 'constantMap', 'count', 'Int'],
    rejected: ['indexed', 'findIndex', 'lookup', 'sliced', 'combined'],
  },
  'Examples/Shallow/records.lean': {
    covered: ['make', 'relabel', 'tagged', 'tagName', 'weird', 'fields', 'duplicate', 'empty'],
    rejected: ['sum', 'find'],
  },
};
let generated = 0;
for (const [file, { covered, rejected }] of Object.entries(expected)) {
  const coverage = await readFile(file, 'utf8');
  for (const name of covered) {
    assert.ok(coverage.includes(`theorem SourceChecks.«${name}».wp`), `missing generated source proof: ${file} ${name}`);
    assert.ok(coverage.includes(`theorem «${name}_source»`), `missing generated source theorem: ${file} ${name}`);
    generated += 1;
  }
  for (const name of rejected) {
    assert.ok(!coverage.includes(`theorem SourceChecks.«${name}».wp`), `unexpected generated source proof: ${file} ${name}`);
  }
}

/** The proof of `name`, from its statement to the public theorem that follows it. */
const block = (text, name) => {
  const start = text.indexOf(`theorem SourceChecks.«${name}».wp`);
  const stop = text.indexOf(`theorem «${name}_source»`, start);
  assert.ok(start >= 0 && stop > start, `missing proof block: ${name}`);
  return [start, stop];
};
const within = (text, name, edit) => {
  const [start, stop] = block(text, name);
  return text.slice(0, start) + edit(text.slice(start, stop)) + text.slice(stop);
};

const good = await readFile('Examples/Tamper/arraysource.lean', 'utf8');
const proof = (name) => new RegExp(`(theorem SourceChecks\\.«${name}»\\.wp[\\s\\S]*?)`);
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/data-source-'));
try {
  const path = resolve(dir, 'Tampered.lean');
  const badCallback = good.replace(
    new RegExp(proof('positiveDoubled').source + '\\(0 : _root_\\.Int\\) ≤'), '$1(1 : _root_.Int) ≤');
  const badResult = good.replace(
    new RegExp(proof('positiveDoubled').source + '\\(«positiveDoubled» «_xs#arg» «_delta#arg»\\)'),
    '$1(«positiveDoubled» «_xs#arg» («_delta#arg» + 1))');
  const badFold = good.replace(
    new RegExp(proof('total').source + '\\(«total» «_xs#arg»\\)'), '$1(«total» (1 :: «_xs#arg»))');
  const badFunction = good.replace(
    /(def SourceChecks\.«total»\.function : Ariadne\.Function := [^\n]*functions\[)1(\]!)/, '$10$2');
  const records = await readFile('Examples/Tamper/recordsource.lean', 'utf8');
  const badField = within(records, 'relabel', (proof) => proof.replaceAll('"label"', '"name"'));
  const badRecord = within(records, 'relabel', (proof) =>
    proof.replace('(«relabel» «_point#arg» «_label#arg»)', '(«relabel» «_point#arg» «_point#arg».«label»)'));
  const badRead = within(records, 'shift', (proof) =>
    proof.replace('(«shift» «_point#arg» «_delta#arg»)', '(«shift» «_point#arg» («_delta#arg» + 1))'));
  const cases = [['callback specification', good, badCallback], ['claimed result', good, badResult],
    ['reduced result', good, badFold], ['source function', good, badFunction],
    ['record field name', records, badField], ['claimed record', records, badRecord],
    ['record field read', records, badRead]];
  for (const [label, original, bad] of cases) {
    assert.ok(bad !== original, `tamper did not match: ${label}`);
    await writeFile(path, bad);
    const rejected = spawnSync('lake', ['env', 'lean', path], {
      encoding: 'utf8', timeout: 300000, maxBuffer: 8e6,
    });
    assert.notEqual(rejected.status, 0, `kernel accepted modified ${label}`);
    assert.ok(rejected.stdout.includes('error'), rejected.stdout + rejected.stderr);
  }
  console.log(`Data source transfer passed: ${generated} generated theorems and ${cases.length} kernel tamper checks.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
