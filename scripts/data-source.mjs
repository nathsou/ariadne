// Generated weakest-precondition source theorems for array functions must be
// emitted for the supported fragment and rejected by the kernel when the
// callback specification, the claimed result or the proved function changes.
import assert from 'node:assert/strict';
import { mkdir, mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';

const coverage = await readFile('Examples/Shallow/arrays.lean', 'utf8');
const names = ['transform', 'sum', 'find', 'allPositive', 'anyPositive', 'copy', 'constantMap', 'count', 'Int'];
for (const name of names) {
  assert.ok(coverage.includes(`theorem SourceChecks.«${name}».wp`), `missing generated source proof: ${name}`);
  assert.ok(coverage.includes(`theorem «${name}_source»`), `missing generated source theorem: ${name}`);
}
for (const name of ['indexed', 'findIndex', 'lookup', 'sliced', 'combined']) {
  assert.ok(!coverage.includes(`theorem SourceChecks.«${name}».wp`), `unexpected generated source proof: ${name}`);
}

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
  for (const [label, bad] of [['callback specification', badCallback], ['claimed result', badResult],
    ['reduced result', badFold], ['source function', badFunction]]) {
    assert.ok(bad !== good, `tamper did not match: ${label}`);
    await writeFile(path, bad);
    const rejected = spawnSync('lake', ['env', 'lean', path], {
      encoding: 'utf8', timeout: 300000, maxBuffer: 8e6,
    });
    assert.notEqual(rejected.status, 0, `kernel accepted modified ${label}`);
    assert.ok(rejected.stdout.includes('error'), rejected.stdout + rejected.stderr);
  }
  console.log(`Data source transfer passed: ${names.length} generated array theorems and 4 kernel tamper checks.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
