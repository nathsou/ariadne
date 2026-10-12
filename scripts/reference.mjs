// Executable acceptance specifications. These finite tests do not replace M3 proofs.
import assert from 'node:assert/strict';
import { choose } from '../examples/reference/decision.ts';
import { Registers } from '../examples/reference/registers.ts';
import { Tree } from '../examples/reference/tree.ts';

function* permutations(xs) {
  if (!xs.length) { yield []; return; }
  for (let i = 0; i < xs.length; ++i) {
    for (const rest of permutations(xs.filter((_, j) => i !== j))) {
      yield [xs[i], ...rest];
    }
  }
}
const candidates = [
  { kind: 'valid', version: 1, id: 'a' },
  { kind: 'valid', version: 2, id: 'a' },
  { kind: 'valid', version: 2, id: 'b' },
  { kind: 'rejected', reason: 'offline' },
];
for (const floor of [-1, 1, 2, 3]) {
  for (const xs of permutations(candidates)) {
    const result = choose(xs, floor);
    assert.ok(result === undefined || xs.includes(result));
    assert.ok(result === undefined || (result.kind === 'valid' && result.version >= floor));
    assert.deepEqual(result, choose(candidates, floor));
  }
}
assert.equal(choose([], 0), undefined);

const operations = [
  ['a', 'b', 1, '1'], ['a', 'b', 2, '2'], ['a', 'c', 3, '3'], ['a', 'b', 1, '1'],
];
for (const ops of permutations(operations)) {
  const store = new Registers();
  for (const op of ops) { store.write(...op); }
  assert.equal(store.read('a', 'b'), 2);
  assert.equal(store.read('a', 'c'), 3);
  assert.equal(store.read('a', 'd'), undefined);
  for (const op of ops) { store.write(...op); }
  assert.equal(store.read('a', 'b'), 2);
  assert.equal(store.read('a', 'c'), 3);
}
for (const values of permutations([1, 3, 2, 3])) {
  const store = new Registers();
  for (const value of values) { store.count('k', 'r', value); }
  assert.equal(store.counter('k', 'r'), 3);
  assert.equal(store.counter('k', 'other'), 0);
}

const nodes = ['a', 'b', 'c'];
const moves = nodes.flatMap(node => [undefined, ...nodes].map(parent => [node, parent]));
let traces = 0;
// All traces of three moves; validate every prefix, including cycles/self moves.
for (const a of moves) for (const b of moves) for (const c of moves) {
  const tree = new Tree();
  for (const node of nodes) { tree.add(node); }
  for (const move of [a, b, c]) {
    tree.move(...move);
    for (const node of nodes) {
      let cursor = node;
      for (let i = 0; i < nodes.length; ++i) {
        const parent = tree.parent(cursor);
        if (parent === undefined) { break; }
        cursor = parent;
      }
      assert.equal(tree.parent(cursor), undefined);
      assert.equal(tree.root(node), cursor);
      for (const parent of nodes) {
        const children = tree.childList(parent);
        assert.equal(new Set(children).size, children.length);
        assert.equal(children.includes(node), tree.parent(node) === parent);
      }
    }
  }
  ++traces;
}
console.log(`Reference specifications passed: decision/store permutations and ${traces} tree traces.`);
