// Moves (ownership rule 2): a declaration may take over an owned local that
// is never used again. The emitted definitions must agree with the TypeScript
// source and with the original evaluator, where both names share one object.
import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/moves.ts';

const cases = {
  build: [[0n], [-3n], [10n ** 20n]],
  handoff: [[[]], [[1n, 2n]], [[-5n, 5n, 7n]]],
  chain: [[0n], [4n]],
  scoped: [[true], [false]],
};
const lists = new Set(['build', 'chain', 'scoped']);
const argument = value => typeof value === 'boolean' ? `${value}`
  : Array.isArray(value) ? `[${value.map(argument)}]` : `(${value} : Int)`;
const encode = value => typeof value === 'boolean' ? `(.boolean ${value})` : `(.bigint ${argument(value)})`;
const observe = value => Array.isArray(value)
  ? ['array', value.map(x => ['bigint', x.toString()])] : ['bigint', value.toString()];
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shallow-moves-'));
try {
  let runner = 'import Examples.Shallow.moves\nimport Ariadne.Observe\nopen Ariadne\n';
  const expected = [];
  for (const [name, inputs] of Object.entries(cases)) {
    for (const args of inputs) {
      const before = structuredClone(args);
      const result = native[name](...args);
      assert.deepEqual(args, before, `${name} must preserve readonly inputs`);
      expected.push(observe(result), { ok: observe(result) });
      const call = `(Extracted_moves.Shallow.${name} ${args.map(argument).join(' ')})`;
      const bigint = 'fun (x : Int) => Lean.Json.arr #[Lean.toJson "bigint", Lean.toJson (toString x)]';
      const shallow = lists.has(name)
        ? `Lean.Json.arr #[Lean.toJson "array", Lean.Json.arr ((${call}.map (${bigint})).toArray)]`
        : `(${bigint}) ${call}`;
      runner += `#eval IO.println (${shallow}).compress\n`;
      const heap = [];
      const encoded = args.map(arg => {
        if (!Array.isArray(arg)) return encode(arg);
        heap.push(`.array [${arg.map(x => `Value.bigint ${argument(x)}`)}]`);
        return `.ref ${heap.length - 1}`;
      });
      runner += `#eval IO.println ((observeResult (Ariadne.apply Extracted_moves.program 3000 { heap := [${heap}] } (.function "${name}") [${encoded}])).compress)\n`;
    }
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const result = spawnSync('lake', ['env', 'lean', path], { encoding: 'utf8', timeout: 300000, maxBuffer: 8e6 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').map(JSON.parse), expected);
  console.log(`Shallow moves passed: ${expected.length / 2} three-way comparisons with readonly input preservation.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
