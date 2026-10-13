// Test-only harness: validates the trusted model against JavaScript. Runs every
// zero-argument export of V2Tests/model/*.ts in Bun (or Node) and in the model.
// `t_*` must agree; `fault_*` must make the model fault (behaviour it refuses to
// model), whatever JavaScript does.
import { readdir } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { observe } from './v2-observe.mjs';

const cli = resolve('.lake/build/bin/ariadne2');
const dir = resolve(process.argv[2] ?? 'V2Tests/model');
let checked = 0;
let failures = 0;
for (const file of (await readdir(dir)).filter(f => f.endsWith('.ts')).sort()) {
  const path = resolve(dir, file);
  const module = await import(pathToFileURL(path).href);
  const names = Object.keys(module).filter(n => n.startsWith('t_') || n.startsWith('fault_')).sort();
  const run = spawnSync(cli, ['batch', path], { input: names.map(n => JSON.stringify([n])).join('\n') + '\n', encoding: 'utf8' });
  if (run.status !== 0) throw new Error(`${file}: ${run.stderr}`);
  const results = run.stdout.trim().split('\n').map(l => JSON.parse(l));
  names.forEach((name, i) => {
    const model = results[i];
    checked++;
    if (name.startsWith('fault_')) {
      if (model[0] !== 'error') { failures++; console.error(`${file}:${name}: expected a model fault, got ${JSON.stringify(model)}`); }
      return;
    }
    let expected;
    try { expected = observe(module[name]()); } catch (e) { expected = ['throws', String(e)]; }
    if (JSON.stringify(expected) !== JSON.stringify(model)) {
      failures++;
      console.error(`${file}:${name}:\n  js    ${JSON.stringify(expected)}\n  model ${JSON.stringify(model)}`);
    }
  });
}
if (failures > 0) { console.error(`V2 model validation: ${failures} of ${checked} failed.`); process.exit(1); }
console.log(`V2 model validation passed: ${checked} cases.`);
