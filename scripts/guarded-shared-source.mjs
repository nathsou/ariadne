import { resolve } from 'node:path';
import { mkdir, mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/guardedshared.ts';

const max = 9007199254740991;
const cases = {
  nested: [[[true, 2], true], [[false, 2], true], [[true, -1], true], [[true, max], false], [[false, max], false]],
  flattened: [[[true, 2], true], [[false, 2], true], [[true, -1], true], [[false, max - 1], true], [[true, max - 1], false], [[false, max], false]],
  nestedFlattened: [[[true, 2], true], [[false, 2], true], [[false, max], true], [[true, max], false], [[false, -max], false]],
  early: [[[true, 2], true], [[false, 2], true], [[false, max], true], [[true, max], false], [[false, -max], false]],
  empty: [[[0], true], [[max], true], [[-max], true], [[max + 1], false]],
  innerJoin: [[[true, true, 2], true], [[true, false, 2], true], [[false, true, 2], true], [[false, false, 2], true], [[true, true, max], false]],
  branchArithmetic: [[[true, 2, 3], true], [[false, -7, 3], true], [[false, 1, 1], true], [[true, 1, -1], false], [[false, -1, -1], false], [[true, max, 2], false]],
  mathScoped: [[[true, -2], true], [[false, -2], true], [[false, -max], true], [[true, -max], false]],
};
const artifact = await readFile('Examples/Shallow/guardedshared.lean', 'utf8');
for (const name of Object.keys(cases)) {
  assert.ok(artifact.includes(`theorem «${name}_source»`), `missing source theorem: ${name}`);
  assert.ok(artifact.includes(`(safe : «${name}».safe`), `missing computed guard: ${name}`);
}
const bits = value => {
  const buffer = new DataView(new ArrayBuffer(8));
  buffer.setFloat64(0, Number.isNaN(value) ? NaN : value);
  return buffer.getBigUint64(0).toString();
};
const argument = value => typeof value === 'boolean' ? String(value) : `(${value} : Int)`;
const source = value => typeof value === 'boolean' ? `.boolean ${value}` : `.number (Float.Model.ofInt (${value}))`;
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/guarded-shared-'));
try {
  let runner = 'import Examples.Shallow.guardedshared\nimport Ariadne.Observe\nopen Ariadne\nopen Extracted_guardedshared.Shallow\n';
  const expected = [];
  let count = 0;
  for (const [name, entries] of Object.entries(cases)) for (const [args, safe] of entries) {
    const argumentsText = args.map(argument).join(' ');
    runner += `#eval IO.println (Lean.toJson (decide (${name}.safe ${argumentsText}))).compress\n`;
    expected.push(safe);
    const observed = { ok: ['number', bits(native[name](...args))] };
    runner += `#eval IO.println ((observeResult (Ariadne.apply Extracted_guardedshared.program 10000 {} (.function "${name}") [${args.map(source)}])).compress)\n`;
    expected.push(observed);
    if (safe) {
      runner += `#eval IO.println ((observeResult (.ok (.number (Float.Model.ofInt (${name} ${argumentsText})), {}))).compress)\n`;
      expected.push(observed);
    }
    count++;
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const checked = spawnSync('lake', ['env', 'lean', path], { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
  assert.equal(checked.status, 0, checked.stdout + checked.stderr);
  assert.deepEqual(checked.stdout.trim().split('\n').map(JSON.parse), expected);
  // Recheck only one small generated function for each forged witness.
  const good = await readFile('Examples/Tamper/guardedshared.lean', 'utf8');
  const badCapture = good.replace(/(def SourceJoinChecks\.«nested#select[^»]*» :[\s\S]*?\n\s*\| _, \.here => )[^\n]+/, '$1Core.Var.here');
  const badOperation = good.replace(/(theorem SourceJoinChecks\.«nested#suffix[^»]*»[\s\S]*?exact[\s\S]*?)Ariadne.Shallow.Core.Binary.intMul/, '$1Ariadne.Shallow.Core.Binary.intAdd');
  const badGuard = good.replace('safe.2\n', '(by rfl)\n');
  const tampered = resolve(dir, 'Tampered.lean');
  for (const [label, bad] of [['capture', badCapture], ['suffix operation', badOperation], ['computed guard', badGuard]]) {
    assert.ok(bad !== good, `tamper did not match ${label}`);
    await writeFile(tampered, bad);
    const rejected = spawnSync('lake', ['env', 'lean', tampered], { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
    assert.notEqual(rejected.status, 0, `kernel accepted modified ${label}`);
    assert.ok(rejected.stdout.includes('error'), rejected.stdout + rejected.stderr);
  }
  console.log(`Guarded shared source transfer passed: 8 universal theorems, ${count} guard/operational comparisons and 3 kernel tamper checks.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
