// Thrown errors: the TypeScript source, the emitted definitions (which return
// `Sum.inl message` for a throw) and the original evaluator (which fails with
// `Fault.thrown message`) must agree on every result and every message.
import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/throws.ts';

const cases = {
  checked: [[-1n], [0n], [21n]],
  relay: [[0n], [1n], [5n]],
  firstNegative: [[[]], [[1n, 2n]], [[3n, -1n, 4n]], [[-5n]]],
  validate: [[0n], [3n]],
  always: [[]],
};
const units = message => `[${[...message].map(c => c.charCodeAt(0)).join(', ')}]`;
const argument = value => Array.isArray(value) ? `[${value.map(argument)}]` : `(${value} : Int)`;
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-throws-'));
try {
  let runner = 'import Examples.Shallow.throws\nimport Ariadne.Observe\nopen Ariadne\n';
  const expected = [];
  for (const [name, inputs] of Object.entries(cases)) {
    for (const args of inputs) {
      let outcome;
      try {
        outcome = { value: native[name](...args) };
      } catch (error) {
        assert.ok(error instanceof Error, `${name} threw a non-Error`);
        outcome = { message: error.message };
      }
      if ('message' in outcome) {
        expected.push(`thrown ${units(outcome.message)}`, { error: `Ariadne.Fault.thrown ${units(outcome.message)}` });
      } else {
        const value = outcome.value === undefined ? '()' : outcome.value.toString();
        const observed = outcome.value === undefined ? ['undefined'] : ['bigint', outcome.value.toString()];
        expected.push(`value ${value}`, { ok: observed });
      }
      const call = `(Extracted_throws.Shallow.${name} ${args.map(argument).join(' ')})`;
      runner += `#eval IO.println (Lean.toJson (match ${call} with | .inl m => s!"thrown {m}" | .inr v => s!"value {v}")).compress\n`;
      const heap = [];
      const encoded = args.map(arg => {
        if (!Array.isArray(arg)) return `(.bigint ${argument(arg)})`;
        heap.push(`.array [${arg.map(x => `Value.bigint ${argument(x)}`)}]`);
        return `.ref ${heap.length - 1}`;
      });
      runner += `#eval IO.println ((observeResult (Ariadne.apply Extracted_throws.program 3000 { heap := [${heap}] } (.function "${name}") [${encoded}])).compress)\n`;
    }
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], { encoding: 'utf8', timeout: 300000, maxBuffer: 8e6 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  // `reprStr` wraps long faults across lines.
  const actual = result.stdout.trim().split('\n').map(JSON.parse)
    .map(entry => entry?.error ? { error: entry.error.replace(/\s+/g, ' ') } : entry);
  assert.deepEqual(actual, expected);
  console.log(`Shallow throws passed: ${expected.length / 2} three-way comparisons of results and thrown messages.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
