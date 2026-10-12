// Recursive linking, evaluation-order, and printed-table certificate checks.
import { mkdir, mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import assert from 'node:assert/strict';
import { observe, lean } from './scalar-observations.mjs';

const cases = {
  countdown: [[-5n], [0n], [1n], [8n], [25n]],
  parity: [[0n], [1n], [2n], [37n], [-38n]],
  fibonacci: [[-1n], [0n], [1n], [2n], [8n], [12n]],
  collatz: [[1n, 100n], [27n, 200n], [27n, 10n], [0n, 20n], [4n, -1n]],
  scalars: [['abc', 0], ['A😀B', 1], ['', 0], ['test', NaN], ['test', Infinity]],
  ackermann: [[0n, 0n], [1n, 3n], [2n, 2n], [3n, 2n]],
  localFrames: [[0n], [1n], [12n], [-3n]],
  shortCircuit: [[false], [true]],
  argumentOrder: [[false], [true]],
};
const run = (cmd, args) => spawnSync(cmd, args, { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
const cli = args => run('.lake/build/bin/ariadne', args);
const divisionFault = { error: 'Ariadne.Fault.rangeError "bigint division by zero"' };
const conversionFault = { error: 'Ariadne.Fault.rangeError "BigInt requires a finite integer"' };
const timeout = { error: 'Ariadne.Fault.timeout' };
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/recursion-'));
try {
  let runner = [...Object.keys(cases), 'forever'].map(name => `import Examples.Recursive.${name}`).join('\n');
  runner += '\nimport Ariadne.Observe\nopen Ariadne\n';
  runner += 'def observeScalarResult (r : Result Value) : Lean.Json := observeResult (r.map (fun v => (v, {})))\n';
  const expected = [];
  for (const [name, inputs] of Object.entries(cases)) {
    const module = await import(pathToFileURL(resolve(`examples/recursive/${name}.ts`)).href);
    for (const args of inputs) {
      try {
        expected.push({ ok: observe(module[name](...args)) });
      } catch (error) {
        assert.ok(error instanceof RangeError);
        expected.push(name === 'argumentOrder' && args[0] ? conversionFault : divisionFault);
      }
      const arguments_ = `[${args.map(lean).join(', ')}]`;
      runner += `#eval IO.println ((observeScalarResult (Recursive_${name}.compiled_ts_${name} 2000 ${arguments_})).compress)\n`;
      // A poison reference-call handler demonstrates the named/builtin path is
      // sufficient for these executions. The general linker proof is separate.
      runner += `#eval IO.println ((observeResult (Target.link (fun _ _ _ _ => .error (.invariant "external call")) ` +
        `Recursive_${name}.compiled_definitions 2000 2000 {} (.function "${name}") ${arguments_})).compress)\n`;
    }
  }
  const budgets = [0, 1, 2, 5, 12, 24, 48, 96];
  for (const name of Object.keys(cases)) {
    const args = cases[name].at(-1);
    const arguments_ = `[${args.map(lean).join(', ')}]`;
    for (const fuel of budgets) {
      runner += `#eval IO.println ((Lean.Json.arr #[` +
        `observeScalarResult (Recursive_${name}.compiled_ts_${name} ${fuel} ${arguments_}), ` +
        `observeScalarResult (Recursive_${name}.ts_${name} ${fuel} ${arguments_})]).compress)\n`;
    }
  }
  // Do not run the diverging function in the JavaScript host.
  for (const fuel of budgets) {
    runner += `#eval IO.println ((observeScalarResult (Recursive_forever.compiled_ts_forever ${fuel} [])).compress)\n`;
  }
  const runnerPath = resolve(dir, 'Differential.lean');
  await writeFile(runnerPath, runner);
  const result = run('lake', ['env', 'lean', runnerPath]);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  const actual = result.stdout.trim().split('\n').map(line => JSON.parse(line));
  let index = 0;
  for (const value of expected) {
    assert.deepEqual(actual[index++], value);
    assert.deepEqual(actual[index++], value, 'reference compatibility handler must not be used');
  }
  for (let i = 0; i < Object.keys(cases).length * budgets.length; i++) {
    const [compiled, model] = actual[index++];
    assert.deepEqual(compiled, model, 'linking must preserve exact fuel and fault behavior');
  }
  for (const _ of budgets) assert.deepEqual(actual[index++], timeout);
  assert.equal(index, actual.length);

  const source = resolve(dir, 'input.ts');
  const artifact = resolve(dir, 'Output.lean');
  const good = await readFile('Examples/Recursive/countdown.lean', 'utf8');
  const boundary = good.indexOf('def compiled_definitions');
  assert.ok(boundary > 0);
  const changed = good.slice(0, boundary) + good.slice(boundary).replace('name := "countdown"', 'name := "mislinked"');
  assert.notEqual(changed, good);
  await writeFile(artifact, changed);
  const rejected = run('lake', ['env', 'lean', artifact]);
  assert.notEqual(rejected.status, 0, 'modified linked tables must invalidate compilation_checked');
  assert.ok(rejected.stdout.includes('kernel'), rejected.stdout + rejected.stderr);

  await writeFile(source, 'function legacy(): number { const xs = [1]; return xs.length; } ' +
    'function helper(): bigint { return 1n; } export function entry(): bigint { return helper(); }');
  const negative = cli(['compile', source, 'entry', '--out', artifact, '--json']);
  assert.equal(negative.status, 1);
  const diagnostic = JSON.parse(negative.stdout);
  assert.equal(diagnostic.code, 'A4101');
  assert.ok(diagnostic.notes.some(note => note.includes("function 'legacy'")));
  assert.equal(await readFile(artifact, 'utf8'), changed);

  // A call-free entry still compiles without imposing linked-unit restrictions.
  await writeFile(source, 'function legacy(): number { const xs = [1]; return xs.length; } ' +
    'export function entry(): bigint { return 7n; }');
  const isolated = cli(['compile', source, 'entry', '--out', artifact]);
  assert.equal(isolated.status, 0, isolated.stdout + isolated.stderr);
  console.log(`Recursive compilation passed: ${expected.length} native/poison-handler comparisons, ` +
    `${Object.keys(cases).length * budgets.length} fuel comparisons, divergence observations, and table tampering.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
