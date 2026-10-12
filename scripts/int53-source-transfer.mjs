// Reject changes to the correspondence witness and attempts to discard the
// actual computed safety guard, even while all source/Core certificates remain.
import assert from 'node:assert/strict';
import { mkdir, mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';

const coverage = await readFile('Examples/Shallow/int53.lean', 'utf8');
const names = ['add', 'multiply', 'negate', 'remainder', 'floorDivide', 'truncDivide',
  'absolute', 'widen', 'chooseBranch', 'less', 'equal', 'atMost', 'incrementTwice', 'localAbsolute'];
for (const name of names) {
  assert.ok(coverage.includes(`theorem «${name}_source»`), `missing guarded source theorem: ${name}`);
  assert.ok(coverage.includes(`(safe : «${name}».safe`), `missing computed guard: ${name}`);
}
const good = await readFile('Examples/Tamper/int53.lean', 'utf8');
await mkdir('work', {recursive: true});
const dir = await mkdtemp(resolve('work/int53-source-'));
try {
  const path = resolve(dir, 'Tampered.lean');
  const badMath = good.replace(
    /(theorem SourceChecks\.«floorDivide»\.translated[\s\S]*?exact[^\n]*?\.math )\.floor/,
    '$1.trunc');
  const badInteger = good.replace(
    /(theorem SourceChecks\.«add»\.translated[\s\S]*?exact[^\n]*?)Core.Binary.intAdd/,
    '$1Core.Binary.intSub');
  const badSafety = good.replace('inputs (by constructor <;> rfl) (by decide) safe.2',
    'inputs (by constructor <;> rfl) (by decide) (by rfl)');
  for (const [label, bad] of [['Math primitive', badMath], ['integer operation', badInteger], ['safety premise', badSafety]]) {
    assert.ok(bad !== good, `tamper did not match: ${label}`);
    await writeFile(path, bad);
    const checked = spawnSync('lake', ['env', 'lean', path], {encoding: 'utf8', timeout: 180000, maxBuffer: 8e6});
    assert.notEqual(checked.status, 0, `kernel accepted modified ${label}`);
    assert.ok(checked.stdout.includes('error'), checked.stdout + checked.stderr);
  }
  console.log(`Int53 source transfer passed: ${names.length} universal guarded theorems and 3 kernel tamper checks.`);
} finally {
  await rm(dir, {recursive: true, force: true});
}
