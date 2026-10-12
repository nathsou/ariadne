import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/loops.ts';

const cases = {
  sum: [[[]], [[1n, -3n, 9n]], [[10n ** 40n]]],
  until: [[[], 3n], [[-2n, 1n, 4n, 2n], 3n], [[2n, 3n, -1n], 3n], [[5n], 0n]],
  first: [[[], 0n], [[1n, 5n, 9n], 4n], [[1n, 2n], 3n]],
  nested: [[[], []], [[1n], []], [[1n, 2n], [3n, 4n]],
    [[-1n, 2n], [0n, 3n, -1n, 9n]], [[2n, 100n, 3n], [1n, 2n]]],
  last: [[[]], [[4n]], [[2n, -1n, 3n, 0n]], [[-3n, -9n]], [[10n ** 40n]]],
  localScope: [[[]], [[1n, 2n]], [[-2n, 4n]]],
  nestedNoReturn: [[[]], [[1n, -2n, 3n]], [[10n, 20n, -1n]]],
  switched: [[[]], [[0n, 1n, 3n]], [[1n, 2n, 9n]], [[4n, 0n]]],
  noDefault: [[0n], [1n], [2n]],
  counted: [[0n, 0n], [4n, 2n], [-3n, 3n], [2n, 5n], [10n ** 40n, 10n ** 40n + 2n]],
  countedExits: [[-5n], [0n], [4n], [15n]],
  switchReturn: [[0n], [3n]],
};
const optional = new Set(['first', 'last']);
const argument = value => Array.isArray(value) ? `[${value.map(argument)}]` : `(${value} : Int)`;
const observe = value => value === undefined ? ['undefined'] : ['bigint', value.toString()];
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-loops-'));
try {
  let runner = 'import Examples.Shallow.loops\nimport Ariadne.Observe\nopen Ariadne\n';
  const expected = [];
  for (const [name, inputs] of Object.entries(cases)) {
    for (const args of inputs) {
      const before = structuredClone(args);
      const result = native[name](...args);
      assert.deepEqual(args, before, `${name} must preserve readonly inputs`);
      expected.push({ ok: observe(result) }, { ok: observe(result) });
      const call = `(Extracted_loops.Shallow.${name} ${args.map(argument).join(' ')})`;
      const value = optional.has(name) ? `((${call}.map Value.bigint).getD .undefined)` : `(.bigint ${call})`;
      runner += `#eval IO.println ((observeResult (.ok (${value}, {}))).compress)\n`;
      const heap = [];
      const encoded = args.map(arg => {
        if (!Array.isArray(arg)) return `(.bigint ${argument(arg)})`;
        const ref = `.ref ${heap.length}`;
        heap.push(`.array [${arg.map(x => `Value.bigint ${argument(x)}`)}]`);
        return ref;
      });
      runner += `#eval IO.println ((observeResult (Ariadne.apply Extracted_loops.program 3000 { heap := [${heap}] } (.function "${name}") [${encoded}])).compress)\n`;
    }
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').map(JSON.parse), expected);
  console.log(`Shallow loops passed: ${expected.length / 2} three-way comparisons with readonly input preservation.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
