// Test-only harness: each negative fixture names the diagnostic `ariadne
// translate` must report (first line `// expect: CODE`).
import { readdir, readFile, mkdtemp } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve, join } from 'node:path';
import { tmpdir } from 'node:os';

const cli = resolve('.lake/build/bin/ariadne');
const dir = resolve('Tests/negative');
const out = join(await mkdtemp(join(tmpdir(), 'ariadne-')), 'out.lean');
let failures = 0;
const files = (await readdir(dir)).filter(f => f.endsWith('.ts')).sort();
for (const file of files) {
  const path = resolve(dir, file);
  const code = (await readFile(path, 'utf8')).match(/^\/\/ expect: (A\d{4})/)?.[1];
  if (!code) throw new Error(`${file}: missing '// expect: CODE'`);
  const run = spawnSync(cli, ['translate', path, '--out', out, '--namespace', 'Negative'], { encoding: 'utf8' });
  if (run.status !== 1 || !run.stderr.includes(`error ${code}:`)) {
    failures++;
    console.error(`${file}: expected ${code}, got status ${run.status}: ${run.stderr.trim()}`);
  }
}
if (failures > 0) process.exit(1);
console.log(`Negative fixtures passed: ${files.length}.`);
