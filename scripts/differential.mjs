// Test-only harness: runs every exported function of each fixture in Bun (or Node)
// and in the trusted model (`ariadne batch`) on the same inputs and compares the
// observations. Inputs are generated from the checker's resolved parameter types,
// including JavaScript values the types allow beyond the canonical encoding:
// records with extra fields in any order, optional fields absent or `undefined`,
// either nullish value where a type admits both, and omitted trailing arguments.
// A class's methods run on random states: an object of the class whose Map fields
// hold random entries; the model gets the state's observation and returns the
// method's result and the state it leaves, which must match the object's.
//
//   bun scripts/differential.mjs [fixtures dir] [calls per function] [compiled dir]
//
// With a compiled directory, JavaScript runs `<compiled>/<name>.js` for each `<name>.ts` (the file as built
// for production: bundled, minified) while the model runs the source, so the build is tested too.
import { readdir } from 'node:fs/promises';
import { spawn, spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { observe } from './observe.mjs';
import { values } from './values.mjs';

const cli = resolve('.lake/build/bin/ariadne');
const dir = resolve(process.argv[2] ?? 'Tests/fixtures');
const perFunction = Number(process.argv[3] ?? 300);
const compiled = process.argv[4] ? resolve(process.argv[4]) : null;

const { random, pick, chance, value } = values(0x2545f491);

// Inputs are drawn file by file in a fixed order (so a seed always gives the same
// calls); the model's batches then run concurrently.
const jobs = [];
for (const file of (await readdir(dir)).filter(f => f.endsWith('.ts')).sort()) {
  const path = resolve(dir, file);
  const signatures = spawnSync(cli, ['signatures', path], { encoding: 'utf8' });
  if (signatures.status !== 0) throw new Error(`${file}: ${signatures.stderr}`);
  const module = await import(pathToFileURL(compiled ? resolve(compiled, file.replace(/\.ts$/, '.js')) : path).href);
  const lines = [];
  const expected = [];
  for (const sig of signatures.stdout.trim().split('\n').map(l => JSON.parse(l))) {
    if (!sig.exported) continue;
    for (let i = 0; i < perFunction; i++) {
      if (sig.method) {
        // An object of the class with a random state (its fields in declaration order).
        const cls = module[sig.class];
        const self = Object.create(cls.prototype);
        for (const [name, ty] of sig.params[0].fields) self[name] = value(ty);
        const before = observe(self);
        const args = sig.params.slice(1).map(value);
        let result;
        try { result = ['method', observe(self[sig.name](...args)), observe(self)]; } catch (e) { result = ['throws', String(e)]; }
        lines.push(JSON.stringify(['@' + sig.name, before, ...args.map(observe)]));
        expected.push({ call: `${sig.class}.${sig.name}(${args.map(a => observeText(a)).join(', ')}) on ${JSON.stringify(before)}`, result });
        continue;
      }
      if (sig.class !== null) {
        // The constructor: `new C()`.
        let result;
        try { result = observe(new module[sig.class]()); } catch (e) { result = ['throws', String(e)]; }
        lines.push(JSON.stringify([sig.name]));
        expected.push({ call: `new ${sig.class}()`, result });
        continue;
      }
      let args = sig.params.map(value);
      // Omit trailing arguments that may be undefined.
      while (args.length > 0 && args[args.length - 1] === undefined && chance(0.5)) args = args.slice(0, -1);
      let result;
      try { result = observe(module[sig.name](...args)); } catch (e) { result = ['throws', String(e)]; }
      lines.push(JSON.stringify([sig.name, ...args.map(observe)]));
      expected.push({ call: `${sig.name}(${args.map(a => observeText(a)).join(', ')})`, result });
    }
  }
  jobs.push({ file, path, lines, expected });
}

function batch(path, input) {
  return new Promise((resolveRun, reject) => {
    const child = spawn(cli, ['batch', path]);
    let stdout = '';
    let stderr = '';
    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');
    child.stdout.on('data', d => { stdout += d; });
    child.stderr.on('data', d => { stderr += d; });
    child.on('error', reject);
    child.on('close', status => resolveRun({ status, stdout, stderr }));
    child.stdin.end(input);
  });
}

const runs = await Promise.all(jobs.map(({ path, lines }) => batch(path, lines.join('\n') + '\n')));

let calls = 0;
let refused = 0;
let timeouts = 0;
let failures = 0;
for (const [j, { file, expected }] of jobs.entries()) {
  const run = runs[j];
  if (run.status !== 0) throw new Error(`${file}: ${run.stderr}`);
  const actual = run.stdout.trim().split('\n').map(l => JSON.parse(l));
  expected.forEach(({ call, result }, i) => {
    calls++;
    // The model refuses operations outside the subset (numbers leaving the safe
    // range, inconsistent comparators) and makes no claim about them.
    if (actual[i][0] === 'error' && actual[i][1].startsWith('unsupported:')) { refused++; return; }
    // Running out of fuel (100,000 steps) is a fault too: the model makes no claim.
    if (actual[i][0] === 'error' && actual[i][1] === 'timeout') { timeouts++; return; }
    if (JSON.stringify(actual[i]) !== JSON.stringify(result)) {
      failures++;
      if (failures <= 20) console.error(`${file}: ${call}:\n  js    ${JSON.stringify(result)}\n  model ${JSON.stringify(actual[i])}`);
    }
  });
}

function observeText(v) {
  return JSON.stringify(v, (_, x) => (typeof x === 'bigint' ? `${x}n` : x === undefined ? '<undefined>' :
    x instanceof Map ? Object.fromEntries(x) : x));
}

if (failures > 0) {
  console.error(`Differential: ${failures} of ${calls} calls disagree.`);
  process.exit(1);
}
console.log(`Differential passed${compiled ? ' (compiled)' : ''}: ${calls} calls (${refused} refused by the model, ${timeouts} out of fuel).`);
