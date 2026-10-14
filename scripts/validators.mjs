// Test-only harness for `ariadne validators`. For every exported function and method of each fixture:
// - the guard accepts every argument list the differential test draws (values the types allow);
// - on mutated argument lists (a value of the wrong type, a fraction, NaN, a number beyond the safe
//   integers, an array with a hole, a getter, a class instance, a non-string map key, …) wherever the guard
//   accepts, JavaScript and the model give the same result, as they must for represented values;
// - every mutation kind is rejected somewhere (so the guards are not vacuous).
import { readdir, writeFile, mkdtemp, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';
import { observe } from './observe.mjs';
import { values } from './values.mjs';

const cli = resolve('.lake/build/bin/ariadne');
const dir = resolve(process.argv[2] ?? 'Tests/fixtures');
const perFunction = Number(process.argv[3] ?? 100);
const { random, pick, chance, value, strings } = values(0x1badb002);

class Opaque { constructor() { this.x = 1n; } }
/** Values no type in the subset is represented by, or only some are. */
const junk = () => pick([
  ['undefined', undefined], ['null', null], ['fraction', 1.5], ['NaN', NaN], ['infinity', Infinity],
  ['unsafe integer', 2 ** 53], ['string', 'a'], ['bigint', 1n], ['boolean', true], ['empty object', {}],
  ['empty array', []], ['map', new Map()], ['instance', new Opaque()], ['function', () => 0],
]);

/** A mutation of a value of type `ty`: [kind, value]. */
function mutate(ty, v) {
  if (chance(0.4)) return junk();
  switch (ty.t) {
    case 'record': case 'union': {
      const fields = ty.t === 'record' ? ty.fields : (ty.variants.find(x => v[ty.key] === tagValue(x.tag)) ?? ty.variants[0]).fields;
      if (fields.length === 0 || chance(0.2)) return ['inherited', Object.setPrototypeOf({ ...v }, { [ty.t === 'union' ? ty.key : 'x']: 1n })];
      const [f, fty] = pick(fields);
      if (chance(0.25)) {
        const w = { ...v };
        const x = w[f];
        delete w[f];
        return ['getter', Object.defineProperty(w, f, { get: () => x, enumerable: true })];
      }
      const [kind, x] = mutate(fty, v[f]);
      return [kind, { ...v, [f]: x }];
    }
    case 'array': {
      if (v.length === 0) return ['element', [mutate(ty.of, value(ty.of))[1]]];
      if (chance(0.3)) { const w = [...v]; delete w[Math.floor(random() * w.length)]; return ['hole', w]; }
      const i = Math.floor(random() * v.length);
      const [kind, x] = mutate(ty.of, v[i]);
      return [kind, v.map((y, j) => (j === i ? x : y))];
    }
    case 'map': {
      if (chance(0.4)) return ['map key', new Map([...v, [1, value(ty.of)]])];
      const [kind, x] = mutate(ty.of, value(ty.of));
      return [kind, new Map([...v, [pick(strings), x]])];
    }
    case 'option': return v == null ? junk() : mutate(ty.of, v);
    default: return junk();
  }
}
const tagValue = tag => ('bool' in tag ? tag.bool : String.fromCharCode(...tag.value));

const scratch = await mkdtemp(join(tmpdir(), 'ariadne-validators-'));
let accepted = 0, mutants = 0, mutantsAccepted = 0, failures = 0;
const rejectedKinds = new Set();
const allKinds = new Set();
try {
  for (const file of (await readdir(dir)).filter(f => f.endsWith('.ts')).sort()) {
    const path = resolve(dir, file);
    const out = join(scratch, file.replace(/\.ts$/, '.validators.ts'));
    const gen = spawnSync(cli, ['validators', path, '--out', out], { encoding: 'utf8' });
    if (gen.status !== 0) throw new Error(`${file}: ${gen.stderr}`);
    const { args: guards } = await import(pathToFileURL(out).href);
    const module = await import(pathToFileURL(path).href);
    const signatures = spawnSync(cli, ['signatures', path], { encoding: 'utf8' }).stdout.trim().split('\n').map(l => JSON.parse(l));
    const lines = [];
    const expected = [];
    for (const sig of signatures) {
      if (!sig.exported || sig.name.startsWith('new ')) continue;
      const guard = guards[sig.name];
      if (typeof guard !== 'function') throw new Error(`${file}: no guard for ${sig.name}`);
      const params = sig.method ? sig.params.slice(1) : sig.params;
      for (let i = 0; i < perFunction; i++) {
        const args = params.map(value);
        if (!guard(...args)) {
          failures++;
          console.error(`${file}: ${sig.name} rejects represented arguments ${observeText(args)}`);
          continue;
        }
        accepted++;
        const k = Math.floor(random() * Math.max(1, params.length));
        if (params.length === 0) continue;
        const [kind, x] = mutate(params[k], args[k]);
        const mutant = args.map((a, j) => (j === k ? x : a));
        mutants++;
        allKinds.add(kind);
        if (!guard(...mutant)) { rejectedKinds.add(kind); continue; }
        mutantsAccepted++;
        // Accepted: the arguments must be represented, so JavaScript and the model agree.
        let result;
        if (sig.method) {
          const self = Object.create(module[sig.class].prototype);
          for (const [name, ty] of sig.params[0].fields) self[name] = value(ty);
          const before = observe(self);
          try { result = ['method', observe(self[sig.name](...mutant)), observe(self)]; } catch (e) { result = ['throws', String(e)]; }
          lines.push(JSON.stringify(['@' + sig.name, before, ...mutant.map(observe)]));
        } else {
          try { result = observe(module[sig.name](...mutant)); } catch (e) { result = ['throws', String(e)]; }
          lines.push(JSON.stringify([sig.name, ...mutant.map(observe)]));
        }
        expected.push({ call: `${sig.name}(${observeText(mutant)}) [${kind}]`, result });
      }
    }
    if (lines.length === 0) continue;
    const run = spawnSync(cli, ['batch', path], { input: lines.join('\n') + '\n', encoding: 'utf8' });
    // The model refusing an observation (a fraction, say) means the guard accepted a value nothing represents.
    if (run.status !== 0) { failures++; console.error(`${file}: an accepted argument is not a value of the model: ${run.stderr.trim()}`); continue; }
    run.stdout.trim().split('\n').map(l => JSON.parse(l)).forEach((model, i) => {
      if (model[0] === 'error' && (model[1].startsWith('unsupported:') || model[1] === 'timeout')) return;
      if (JSON.stringify(model) === JSON.stringify(expected[i].result)) return;
      failures++;
      if (failures <= 20) console.error(`${file}: ${expected[i].call}\n  js    ${JSON.stringify(expected[i].result)}\n  model ${JSON.stringify(model)}`);
    });
  }
} finally {
  await rm(scratch, { recursive: true, force: true });
}

function observeText(v) {
  return JSON.stringify(v, (_, x) => (typeof x === 'bigint' ? `${x}n` : x === undefined ? '<undefined>' :
    x instanceof Map ? Object.fromEntries(x) : x));
}

const neverRejected = [...allKinds].filter(k => !rejectedKinds.has(k));
if (neverRejected.length > 0) { console.error(`Validators: never rejected ${neverRejected.join(', ')}.`); failures++; }
if (failures > 0) { console.error(`Validators: ${failures} failures.`); process.exit(1); }
console.log(`Validators passed: ${accepted} represented argument lists accepted; of ${mutants} mutated ones, ` +
  `${mutantsAccepted} accepted, and JavaScript and the model agree on them.`);
