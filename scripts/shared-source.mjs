import { mkdir, mkdtemp, writeFile, readFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';
import * as native from '../examples/shallow/shared.ts';

const good = await readFile('Examples/Shallow/shared.lean', 'utf8');
const names = ['nested', 'flattened', 'nestedFlattened', 'early', 'empty', 'greater', 'numberGreater', 'stringGreater'];
for (const name of names) assert.ok(good.includes(`theorem «${name}_source»`), `missing source theorem for ${name}`);
const bits = value => {
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, Number.isNaN(value) ? NaN : value);
  return view.getBigUint64(0).toString();
};
function argument(value) {
  if (typeof value === 'boolean') return String(value);
  if (typeof value === 'bigint') return `(${value} : Int)`;
  if (typeof value === 'number') return `(Float.Model.ofBits ${bits(value)})`;
  return `([${Array.from({ length: value.length }, (_, i) => value.charCodeAt(i)).join(', ')}] : JSString)`;
}
function source(value) {
  const kind = { boolean: 'boolean', bigint: 'bigint', number: 'number', string: 'string' }[typeof value];
  return `(Value.${kind} ${argument(value)})`;
}
const cases = {
  ...Object.fromEntries(['nested', 'flattened', 'nestedFlattened', 'early'].map(name => [name,
    [false, true].flatMap(flag => [-2n, 0n, 9n, 10n ** 40n].map(x => [flag, x]))])),
  empty: [[-2n], [0n], [9n]],
  greater: [[1n, 2n], [2n, 1n], [2n, 2n]],
  numberGreater: [[1, 2], [2, 1], [2, 2], [NaN, 0], [0, NaN], [Infinity, -Infinity], [-0, 0]],
  stringGreater: [['a', 'b'], ['b', 'a'], ['a', 'a'], ['\uff00', '\u{10000}'], ['\ud800', '\ud7ff']],
};
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/shared-source-'));
try {
  let runner = 'import Examples.Shallow.shared\nimport Ariadne.Observe\nopen Ariadne\n';
  const expected = [];
  for (const [name, inputs] of Object.entries(cases)) for (const args of inputs) {
    const result = native[name](...args);
    const call = `(Extracted_shared.Shallow.«${name}» ${args.map(argument).join(' ')})`;
    const kind = typeof result === 'boolean' ? 'boolean' : 'bigint';
    const observed = [kind, typeof result === 'bigint' ? result.toString() : result];
    runner += `#eval IO.println ((observeResult (.ok (Value.${kind} ${call}, {}))).compress)\n`;
    runner += `#eval IO.println ((observeResult (Ariadne.apply Extracted_shared.program 1000 {} (.function "${name}") [${args.map(source).join(', ')}])).compress)\n`;
    expected.push({ ok: observed }, { ok: observed });
  }
  const comparison = resolve(dir, 'Compare.lean');
  await writeFile(comparison, runner);
  const compared = spawnSync('lake', ['env', 'lean', comparison], { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
  assert.equal(compared.status, 0, compared.stdout + compared.stderr);
  assert.deepEqual(compared.stdout.trim().split('\n').map(JSON.parse), expected);

  const changedSource = good.replace(/(def SourceChecks\.«nested»\.function[^\n]*?Ariadne.Stmt.assign\s*\(Ariadne.Expr.var )"x"/, '$1"wrongTarget"');
  const changedCapture = good.replace(/(def SourceJoinChecks\.«nested#select[^»]*» :[\s\S]*?\n\s*\| _, \.here => )[^\n]+/, '$1Core.Var.here');
  const changedRestore = good.replace(/(theorem SourceChecks\.«nested»\.translated[\s\S]*?)\.restore/, '$1.capture');
  const changedOrder = good.replace(/(theorem SourceChecks\.«greater»\.translated[\s\S]*?exact[^\n]*?)\.intGt/, '$1.intGe');
  const tampered = resolve(dir, 'Tampered.lean');
  for (const [label, bad] of [['source assignment', changedSource], ['captured variable', changedCapture], ['scope restoration', changedRestore], ['reversed comparison', changedOrder]]) {
    assert.ok(bad !== good, `tamper did not match ${label}`);
    await writeFile(tampered, bad);
    const rejected = spawnSync('lake', ['env', 'lean', tampered], { encoding: 'utf8', timeout: 120000, maxBuffer: 8e6 });
    assert.notEqual(rejected.status, 0, `kernel accepted modified ${label}`);
    assert.ok(rejected.stdout.includes('error'), rejected.stdout + rejected.stderr);
  }
  console.log(`Shared scalar source transfer passed: ${names.length} universal theorems, ${expected.length / 2} three-way comparisons and 4 kernel tamper checks.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
