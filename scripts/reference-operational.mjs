// Compare reference traces against the operational model. The universal shallow
// proofs and source transfer required by M3/M4 remain separate acceptance gates.
import { readFile, writeFile, mkdir, mkdtemp, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import { choose } from '../examples/reference/decision.ts';
import { Registers } from '../examples/reference/registers.ts';
import { Tree } from '../examples/reference/tree.ts';

function observe(value) {
  if (value === undefined) return ['undefined'];
  if (typeof value === 'string') return ['string', Array.from({ length: value.length }, (_, i) => value.charCodeAt(i))];
  if (typeof value === 'number') {
    const bits = new DataView(new ArrayBuffer(8));
    bits.setFloat64(0, value);
    return ['number', bits.getBigUint64(0).toString()];
  }
  if (Array.isArray(value)) return ['array', value.map(observe)];
  return ['record', Object.entries(value).map(([k, v]) => [k, observe(v)])];
}
const quoted = s => JSON.stringify(s);
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/reference-'));
let count = 0;
async function compare(stem, cases) {
  const source = await readFile(`examples/reference/${stem}.ts`, 'utf8');
  const file = resolve(dir, `${stem}.ts`);
  const wrappers = cases.map((c, i) => `function case${i}(): ${c.type} { ${c.body} }`).join('\n');
  await writeFile(file, source + '\n' + wrappers);
  for (const [i, c] of cases.entries()) {
    const result = spawnSync('.lake/build/bin/ariadne', ['eval', file, `case${i}`, '10000'], {
      encoding: 'utf8', timeout: 30000,
    });
    assert.equal(result.status, 0, result.stdout + result.stderr);
    assert.deepEqual(JSON.parse(result.stdout), { ok: observe(c.expected) }, `${stem}:${i}`);
    ++count;
  }
}
try {
  const inputs = [
    [], [{ kind: 'rejected', reason: 'offline' }],
    [{ kind: 'valid', version: 2, id: '\uff00' }, { kind: 'valid', version: 2, id: '\u{10000}' }],
    [{ kind: 'valid', version: 1, id: 'b' }, { kind: 'valid', version: 2, id: 'a' }],
  ];
  await compare('decision', inputs.flatMap(xs => [-1, 2, 3].map(floor => ({
    type: 'Candidate | undefined',
    body: `return choose(${JSON.stringify(xs).replace(/"(kind|reason|version|id)":/g, "$1:")}, ${floor});`,
    expected: choose(xs, floor),
  }))));
  const writes = [['a', 'b', 1, '1'], ['a', 'b', 4, '3'], ['a', 'b', 2, '2'], ['a', 'c', 9, '4']];
  await compare('registers', [writes, [...writes].reverse(), [...writes, ...writes]].map(ops => {
    const store = new Registers();
    for (const op of ops) store.write(...op);
    return {
      type: '(Int53 | undefined)[]',
      body: `const store = new Registers(); ${ops.map(op => `store.write(${op.map(quoted).join(',')});`).join(' ')} return [store.read('a','b'), store.read('a','c'), store.read('missing','key')];`,
      expected: [store.read('a', 'b'), store.read('a', 'c'), store.read('missing', 'key')],
    };
  }));
  const traces = [[], [['a', 'b'], ['b', 'c']], [['a', 'b'], ['b', 'c'], ['c', 'a']],
    [['a', 'b'], ['a', 'c'], ['b', 'a']], [['a', 'a']], [['a', 'b'], ['a', undefined]]];
  await compare('tree', traces.map(ops => {
    const tree = new Tree();
    for (const op of ops) tree.move(...op);
    const literal = x => x === undefined ? 'undefined' : quoted(x);
    return {
      type: '(string | undefined)[]',
      body: `const tree = new Tree(); ${ops.map(op => `tree.move(${op.map(literal).join(',')});`).join(' ')} return [tree.parent('a'), tree.parent('b'), tree.parent('c'), tree.root('a'), tree.root('b'), tree.root('c')];`,
      expected: ['a', 'b', 'c'].map(x => tree.parent(x)).concat(['a', 'b', 'c'].map(x => tree.root(x))),
    };
  }));
} finally {
  await rm(dir, { recursive: true, force: true });
}
console.log(`Reference operational comparisons passed: ${count} inputs and traces.`);
