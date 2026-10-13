import { readFile, writeFile, mkdir, mkdtemp, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import { Counter, Seeded } from '../examples/shallow/classes.ts';

const traces = [
  ['Counter', [], []],
  ['Counter', [], [['add', 3n], ['twice', 2n], ['add', -5n]]],
  ['Counter', [], [['bump', 'a'], ['bump', 'b'], ['bump', 'a']]],
  ['Counter', [], [['until', ['a', 'b', 'a'], 'stop']]],
  ['Counter', [], [['until', ['a', 'stop', 'b'], 'stop'], ['bump', 'b']]],
  ['Counter', [], [['until', ['stop', 'a'], 'stop']]],
  ['Counter', [], [['bump', '\ud800'], ['bump', '\0'], ['bump', '\ud800']]],
  ...[-7n, 0n, 5n].map(initial => ['Seeded', [initial], [['add', 2n], ['add', -3n]]]),
];
const keys = ['a', 'b', '\ud800', '\0'];
const units = value => Array.from({length: value.length}, (_, i) => value.charCodeAt(i));
const lean = value => typeof value === 'bigint' ? `(${value} : Int)` :
  typeof value === 'string' ? `([${units(value)}] : JSString)` : `[${value.map(lean)}]`;
const expr = value => typeof value === 'bigint' ? `(.literal (.bigint (${value})) {})` : typeof value === 'string' ? `(.literal (.string ${lean(value)}) {})` : `(.array [${value.map(expr)}] {})`;
const observed = values => ({ok: ['array', values.map(value => ['bigint', value.toString()])]});
await mkdir('work', {recursive: true});
const dir = await mkdtemp(resolve('work/shallow-classes-'));
try {
  let runner = 'import Examples.Shallow.classes\nimport Examples.ClassAdequacy\nimport Examples.ClassConstructionAdequacy\nimport Ariadne.Observe\nopen Ariadne\nopen Extracted_classes.Shallow\nset_option linter.unusedVariables false\n' +
    '#check @Examples.ClassAdequacy.seeded_add_source\n' +
    '#check @Examples.ClassAdequacy.seeded_read_source\n' +
    '#check @Examples.ClassAdequacy.seeded_trace_source\n' +
    '#check @Examples.ClassAdequacy.counter_bump_source\n' +
    '#check @Examples.ClassAdequacy.counter_count_source\n' +
    '#check @Examples.ClassAdequacy.counter_trace_source\n' +
    '#check @Examples.ClassAdequacy.seeded_constructor_source\n' +
    '#check @Examples.ClassAdequacy.counter_constructor_source\n' +
    '#check @Examples.ClassAdequacy.seeded_fresh_trace_source\n' +
    '#check @Examples.ClassAdequacy.counter_fresh_trace_source\n' +
    '#check @Examples.ClassAdequacy.seeded_add_wrapper_source\n' +
    '#check @Examples.ClassAdequacy.seeded_read_wrapper_source\n' +
    '#check @Examples.ClassAdequacy.counter_bump_wrapper_source\n' +
    '#check @Examples.ClassAdequacy.counter_count_wrapper_source\n';
  const expected = [];
  for (const [i, [name, args, ops]] of traces.entries()) {
    const value = new ({Counter, Seeded}[name])(...args);
    const results = [];
    runner += `def trace${i} : List Int := Id.run do\n  let value0 := «${name}##new» ${args.map(lean).join(' ')}\n`;
    const nativeResults = [];
    let model = `def model${i} : Result (Value × State) := do\n  let (receiver, state) ← evalExpr Extracted_classes.program 10000 {} (.newClass "${name}" [${args.map(expr)}] {})\n  let .ref location := receiver | throw (.typeError "class reference expected")\n`;
    const modelResults = [];
    const call = (method, args, save) => {
      model += `  let (args, state) ← evalArgs Extracted_classes.program 10000 state [${args.map(expr)}]\n  let (${save}, state) ← apply Extracted_classes.program 10000 state (.method location "${method}") args\n`;
    };
    const snapshot = (step) => {
      call('read', [], `observed${step}`);
      modelResults.push(`observed${step}`);
      results.push(value.read());
      nativeResults.push(`«${name}#read» value${step}`);
      if (name === 'Counter') for (const key of keys) {
        const saved = `observed${step}key${keys.indexOf(key)}`;
        call('count', [key], saved);
        modelResults.push(saved);
        results.push(value.count(key));
        nativeResults.push(`«Counter#count» value${step} ${lean(key)}`);
      }
    };
    snapshot(0);
    for (const [j, [method, ...arguments_]] of ops.entries()) {
      const result = value[method](...arguments_);
      call(method, arguments_, `result${j}`);
      runner += `  let result${j} := «${name}#${method}» value${j} ${arguments_.map(lean).join(' ')}\n  let value${j+1} := result${j}.2.1\n`;
      if (typeof result === 'bigint') {
        results.push(result);
        modelResults.push(`result${j}`);
        nativeResults.push(`result${j}.1`);
      }
      snapshot(j+1);
    }
    runner += `  return [${nativeResults.join(', ')}]\n#eval IO.println ((observeResult (.ok (.ref 0, {heap := [.array (trace${i}.map Value.bigint)]})))).compress\n`;
    expected.push(observed(results));
    model += `  let (location, state) := state.alloc (.array [${modelResults}])\n  return (.ref location, state)\n#eval IO.println ((observeResult model${i}).compress)\n`;
    runner += model;
    expected.push(observed(results));
  }
  const path = resolve(dir, 'Compare.lean');
  await writeFile(path, runner);
  const native = spawnSync('lake', ['env', 'lean', path], {encoding:'utf8', timeout:120000, maxBuffer:8e6});
  assert.equal(native.status, 0, native.stdout + native.stderr);
  assert.deepEqual(native.stdout.trim().split('\n').filter(line => line.startsWith('{')).map(JSON.parse), expected);
  // Recheck only the handwritten source witnesses. Their generated dependency
  // is imported from the already checked module, avoiding repeated extraction checks.
  const witness = await readFile('Examples/ClassAdequacy.lean', 'utf8');
  const alterations = [
    witness.replace('layout.Holds after.heap (.ref address) («Seeded#add» native amount).2.1 owned',
      'layout.Holds after.heap (.ref address) native owned'),
    witness.replace('before (.method address "add")', 'before (.method address "read")'),
    witness.replace('(input : layout.Holds before.heap (.ref address) native owned)', '(input : True)'),
    witness.replace('counterLayout.Holds after.heap (.ref address) («Counter#bump» native key).2.1 owned',
      'counterLayout.Holds after.heap (.ref address) native owned'),
    witness.replace('(.bigint («Counter#bump» native key).1)', '(.bigint 0)'),
    witness.replace('before (.method address "bump")', 'before (.method address "count")'),
  ];
  for (const [i, altered] of alterations.entries()) {
    assert.notEqual(altered, witness);
    const path = resolve(dir, `TamperedClass${i}.lean`);
    await writeFile(path, altered);
    const refused = spawnSync('lake', ['env', 'lean', path], {encoding:'utf8', timeout:60000, maxBuffer:8e6});
    assert.notEqual(refused.status, 0, 'a forged class source witness must fail kernel checking');
    assert.ok(refused.stdout.includes('error'), refused.stdout + refused.stderr);
  }
  const constructorWitness = await readFile('Examples/ClassConstructionAdequacy.lean', 'utf8');
  const constructorAlterations = [
    constructorWitness.replace('(«Seeded##new» initial) [before.heap.length]',
      '(NativeTypes.«Seeded#state».mk (initial + 1)) [before.heap.length]'),
    constructorWitness.replace('(.newClass "Seeded" [.literal (.bigint initial) {}] {})',
      '(.newClass "Seeded" [.literal (.bigint (initial + 1)) {}] {})'),
    constructorWitness.replace('«Counter##new»\n        [before.heap.length + 1, before.heap.length]',
      '«Counter##new»\n        [before.heap.length + 1]'),
  ];
  for (const [i, altered] of constructorAlterations.entries()) {
    assert.notEqual(altered, constructorWitness);
    const path = resolve(dir, `TamperedConstructor${i}.lean`);
    await writeFile(path, altered);
    const refused = spawnSync('lake', ['env', 'lean', path], {encoding:'utf8', timeout:60000, maxBuffer:8e6});
    assert.notEqual(refused.status, 0, 'a forged constructor witness must fail kernel checking');
    assert.ok(refused.stdout.includes('error'), refused.stdout + refused.stderr);
  }
  console.log(`Shallow classes passed: ${traces.length} three-way constructor/method traces with intermediate state observations, 14 universal source/constructor/wrapper/trace witnesses, and 9 class tamper checks.`);
} finally { await rm(dir, {recursive:true, force:true}); }
