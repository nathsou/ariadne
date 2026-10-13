// Measured while loops: the emitted definitions must agree with the TypeScript
// source and with the original evaluator, and the extracted safety condition
// must hold exactly when every continuing step decreases the stated measure.
import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/measured.ts';

const cases = {
  gcd: [[0n, 0n], [12n, 18n], [-21n, 14n], [17n, 5n], [7n, 0n]],
  countdown: [[-4n], [0n], [1n], [9n]],
  doubling: [[0n], [1n], [5n], [64n], [5000n]],
  root: [[0n, 0n], [10n, 49n], [10n, 50n], [3n, 16n]],
  climb: [[12n], [10n], [9n], [0n]],
};
// The measure of `climb` grows whenever its loop continues.
const decreasing = (name, args) => name !== 'climb' || args[0] >= 10n;
const argument = value => `(${value} : Int)`;
const observe = value => ['bigint', value.toString()];
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-measured-'));
try {
  let runner = 'import Examples.Shallow.measured\nimport Ariadne.Observe\nopen Ariadne\n';
  const expected = [];
  for (const [name, inputs] of Object.entries(cases)) {
    for (const args of inputs) {
      const result = native[name](...args);
      expected.push({ name, args, ok: observe(result), safe: decreasing(name, args) });
      const call = `(Extracted_measured.Shallow.${name} ${args.map(argument).join(' ')})`;
      runner += `#eval IO.println ((observeResult (.ok (.bigint ${call}, {}))).compress)\n`;
      runner += `#eval IO.println ((observeResult (Ariadne.apply Extracted_measured.program 3000 {} (.function "${name}") [${args.map(arg => `.bigint ${argument(arg)}`)}])).compress)\n`;
      runner += `#eval IO.println (decide (Extracted_measured.Shallow.${name}.safe ${args.map(argument).join(' ')}))\n`;
    }
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], { encoding: 'utf8', timeout: 300000, maxBuffer: 8e6 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  const lines = result.stdout.trim().split('\n').map(JSON.parse);
  assert.equal(lines.length, expected.length * 3);
  expected.forEach(({ name, args, ok, safe }, i) => {
    const [shallow, source, checked] = lines.slice(3 * i, 3 * i + 3);
    const label = `${name}(${args.join(', ')})`;
    assert.deepEqual(source, { ok }, `original evaluator disagrees: ${label}`);
    assert.equal(checked, safe, `safety condition: ${label}`);
    // Adequacy is claimed only under the safety condition; without it the
    // bounded denotation may stop early.
    if (safe) assert.deepEqual(shallow, { ok }, `emitted definition disagrees: ${label}`);
  });
  const unsafe = expected.filter(c => !c.safe).length;
  console.log(`Shallow measured loops passed: ${expected.length} source/evaluator comparisons, ` +
    `${expected.length - unsafe} emitted-definition comparisons under the safety condition, ${unsafe} rejected measures.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
