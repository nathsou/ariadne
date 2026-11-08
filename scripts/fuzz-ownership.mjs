// Test-only harness for the ownership rules (Front/Desugar.lean, trusted): random functions that change arrays,
// records and maps in place, alias them in every way the subset can (another name, a call returning its argument,
// an array or record holding them, a shallow record copy, a map holding them, loops, early returns), then return
// what every variable holds. Each function is its own file, translated and run in the model (`ariadne batch`) and in
// Bun. Where Ariadne accepts a function, JavaScript must give what the model gives: an aliasing the rules miss shows
// up as a change in place that JavaScript sees through another name and the model doesn't. Refusals make no claim.
// Weakening a rule makes it fail (each was tried: the escapes, fresh values); the rule for an escape in a loop's later
// iteration is pinned by Tests/negative/owned-next-iteration.ts, which random programs rarely reach.
//
//   bun scripts/fuzz-ownership.mjs [functions]
import { writeFile, mkdtemp } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve, join } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';
import { observe } from './observe.mjs';

const cli = resolve('.lake/build/bin/ariadne');
let seed = Number(process.env.FUZZ_SEED ?? 0x0a11a5ed);
const random = () => ((seed = (Math.imul(seed ^ (seed >>> 15), 0x2c1b3c6d) + 0x6d2b79f5) >>> 0) / 2 ** 32);
const pick = xs => xs[Math.floor(random() * xs.length)];
const chance = p => random() < p;
const num = () => pick(['0', '1', '2', '5', '-3', '9']);

const header = `interface R {
  xs: number[];
  n: number;
}

function id(xs: number[]): number[] {
  return xs;
}

function first(r: R): number[] {
  return r.xs;
}
`;

/** Generates one function's body. Variables by kind: a (number[]), g (number[][]), r (R), m (Map<string, number>),
 * q (Map<string, number[]>). */
function body() {
  let vars = { a: [], g: [], r: [], m: [], q: [] };
  // A block's declarations go out of scope at its end.
  const block = f => { const saved = Object.fromEntries(Object.entries(vars).map(([k, l]) => [k, [...l]])); f(); vars = saved; };
  let k = 0;
  const lines = [];
  const any = kind => (vars[kind].length ? pick(vars[kind]).name : null);
  const arrExpr = () => {
    const a = any('a');
    const choices = [`[${num()}, ${num()}]`, `[]`];
    if (a) choices.push(`[...${a}]`, a, `id(${a})`, `${a}.filter((y) => y > 0)`, `${a}.slice(0, 1)`, `${a}.toSorted((x, y) => x - y)`);
    const g = any('g');
    if (g) choices.push(`${g}[0] ?? []`);
    const r = any('r');
    if (r) choices.push(`${r}.xs`, `first(${r})`);
    const q = any('q');
    if (q) choices.push(`${q}.get("k") ?? []`);
    return pick(choices);
  };
  const decl = (kind, ind) => {
    const x = `${kind}${k++}`;
    const kw = chance(0.5) ? 'let' : 'const';
    let init;
    switch (kind) {
      case 'a': init = `: number[] = ${arrExpr()}`; break;
      case 'g': init = `: number[][] = ${pick([`[${arrExpr()}]`, `[[${num()}]]`, `[${arrExpr()}, ${arrExpr()}]`, any('g') ?? '[]'])}`; break;
      case 'r': init = `: R = ${pick([`{ xs: ${arrExpr()}, n: ${num()} }`, ...(any('r') ? [`{ ...${any('r')} }`, any('r'), `{ ...${any('r')}, n: 4 }`] : [])])}`; break;
      case 'm': init = ` = new Map<string, number>()`; break;
      default: init = ` = new Map<string, number[]>()`; break;
    }
    lines.push(`${ind}${kw} ${x}${init};`);
    vars[kind].push({ name: x, mutable: kw === 'let' });
  };
  const change = ind => {
    const options = [];
    const a = any('a'), g = any('g'), r = any('r'), m = any('m'), q = any('q');
    if (a) options.push(`${a}.push(${num()});`, `${a}.push(${a}.length);`, `${a}.pop();`, `${a}.sort((x, y) => y - x);`);
    if (a && chance(0.3)) options.push(`${a}.push(...${arrExpr()});`);
    if (g) options.push(`${g}.push(${arrExpr()});`, `${g}.pop();`);
    // Storing an array as it is, the likeliest way to alias it.
    if (a && g) options.push(`${g}.push(${a});`);
    if (a && r) options.push(`${r}.xs = ${a};`);
    if (a && q) options.push(`${q}.set("k", ${a});`);
    if (r) options.push(`${r}.n = ${num()};`, `${r}.xs = ${arrExpr()};`);
    if (m) options.push(`${m}.set("k", ${num()});`, `${m}.set("j", ${a ? `${a}.length` : num()});`, `${m}.delete("k");`);
    if (q) options.push(`${q}.set("k", ${arrExpr()});`, `${q}.delete("k");`);
    const lets = [...vars.a, ...vars.g, ...vars.r].filter(v => v.mutable);
    if (lets.length && chance(0.3)) {
      const v = pick(lets);
      const kind = v.name[0];
      options.push(`${v.name} = ${kind === 'a' ? arrExpr() : kind === 'g' ? `[${arrExpr()}]` : `{ xs: ${arrExpr()}, n: 1 }`};`);
    }
    if (options.length) lines.push(ind + pick(options));
  };
  const stmts = (n, depth, ind) => {
    for (let i = 0; i < n; i++) {
      const roll = random();
      if (roll < 0.3) decl(pick(['a', 'a', 'a', 'g', 'r', 'r', 'm', 'q']), ind);
      else if (roll < 0.75) change(ind);
      else if (roll < 0.85 && depth > 0) {
        const a = any('a');
        const x = `x${k++}`;
        lines.push(`${ind}for (const ${x} of ${a && chance(0.4) ? a : '[1, 2, 3]'}) {`);
        block(() => stmts(pick([2, 3, 4]), depth - 1, ind + '  '));
        lines.push(`${ind}}`);
      } else if (roll < 0.93 && depth > 0) {
        lines.push(`${ind}if (${any('a') ? `${any('a')}.length > 1` : 'true'}) {`);
        block(() => stmts(2, depth - 1, ind + '  '));
        lines.push(`${ind}}`);
      } else if (any('a')) lines.push(`${ind}if (${any('a')}.length > 3) return ${observe_()};`);
    }
  };
  // What every variable in scope holds.
  const observe_ = () => '[' + [
    ...vars.a.map(v => v.name),
    ...vars.g.map(v => `...${v.name}`),
    ...vars.r.flatMap(v => [`${v.name}.xs`, `[${v.name}.n]`]),
    ...vars.m.map(v => `[...${v.name}.values()]`),
    ...vars.q.map(v => `...[...${v.name}.values()]`),
  ].join(', ') + ']';
  stmts(10, 2, '  ');
  return `export function f(): number[][] {\n${lines.join('\n')}\n  return ${observe_()};\n}\n`;
}

const dir = await mkdtemp(join(tmpdir(), 'ariadne-ownership-'));
const total = Number(process.argv[2] ?? 400);
let accepted = 0, refused = 0, agreed = 0, modelRefused = 0, failures = 0;
for (let i = 0; i < total; i++) {
  const path = join(dir, `o${i}.ts`);
  const text = header + '\n' + body();
  await writeFile(path, text);
  const run = spawnSync(cli, ['batch', path], { input: JSON.stringify(['f']) + '\n', encoding: 'utf8' });
  if (run.status !== 0) { refused++; continue; }
  accepted++;
  const model = JSON.parse(run.stdout.trim().split('\n')[0]);
  if (model[0] === 'error') { modelRefused++; continue; }
  let js;
  try { js = observe((await import(pathToFileURL(path).href)).f()); } catch (e) { js = ['throws', String(e)]; }
  if (JSON.stringify(js) === JSON.stringify(model)) { agreed++; continue; }
  failures++;
  if (failures <= 5) console.error(`${path}\n  js    ${JSON.stringify(js)}\n  model ${JSON.stringify(model)}`);
}
if (failures > 0) { console.error(`Ownership fuzzing: ${failures} disagreements.`); process.exit(1); }
console.log(`Ownership fuzzing passed: of ${total} functions, ${accepted} accepted (${agreed} agree with JavaScript, ` +
  `${modelRefused} refused by the model), ${refused} refused.`);
