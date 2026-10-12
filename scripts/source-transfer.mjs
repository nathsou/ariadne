// The generated operational witnesses must fail when source bindings, primitive
// rules or the selected source function are changed independently of Core.
import assert from 'node:assert/strict';
import { mkdir, mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';

const good = await readFile('Examples/Shallow/source.lean', 'utf8');
for (const name of ['arithmetic', 'quotient', 'choice_source', 'conjunction',
  'disjunction', 'compare', 'equal', 'text', 'unit', 'local', 'early', 'branchLocal', 'nested']) {
  assert.ok(good.includes(`theorem «${name}_source»`), `missing universal source theorem: ${name}`);
}
assert.ok(good.includes('theorem SourceChecks.«choice».source'));
assert.ok(good.includes('def «choice_source»'));
assert.ok(good.includes('theorem ts_choice.source'));

await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/source-transfer-'));
try {
  const path = resolve(dir, 'Tampered.lean');
  const badRules = good.replace(
    /(theorem SourceChecks\.«arithmetic»\.translated[\s\S]*?exact[^\n]*)\.intAdd/,
    '$1.intSub');
  const badNames = good.replace('Adequacy.Names.fromList ["flag", "x", "y"]',
    'Adequacy.Names.fromList ["flag", "y", "x"]');
  const badFunction = good.replace(
    /(def SourceChecks\.«arithmetic»\.function[^\n]*name := )"arithmetic"/,
    '$1"notTheSourceFunction"');
  const badDeclaration = good.replace(
    /(theorem SourceChecks\.«local»\.translated[\s\S]*?exact[^\n]*?\.let_ )"sum"/,
    '$1"differentName"');
  const badBranch = good.replace(
    /(theorem SourceChecks\.«early»\.translated[\s\S]*?exact[^\n]*?)\.intLt/,
    '$1.intLe');
  for (const [label, bad] of [['primitive rule', badRules], ['parameter names', badNames], ['source function', badFunction], ['local declaration', badDeclaration], ['branch condition', badBranch]]) {
    assert.notEqual(bad, good, `tamper did not match: ${label}`);
    await writeFile(path, bad);
    const rejected = spawnSync('lake', ['env', 'lean', path], {
      encoding: 'utf8', timeout: 120000, maxBuffer: 8e6,
    });
    assert.notEqual(rejected.status, 0, `kernel accepted modified ${label}`);
    assert.ok(rejected.stdout.includes('error'), rejected.stdout + rejected.stderr);
  }
  console.log('Source transfer passed: 14 universal emitted theorems, declaration/branch and name collision coverage, and 5 kernel tamper checks.');
} finally {
  await rm(dir, { recursive: true, force: true });
}
