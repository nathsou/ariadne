import { mkdir, mkdtemp, writeFile, readFile, rm, symlink } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';

await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/cli-'));
const source = resolve(dir, 'input.ts');
const artifact = resolve(dir, 'Model.lean');
const run = (command, args) => spawnSync(command, args, { encoding: 'utf8', timeout: 60000 });
const cli = args => run('.lake/build/bin/ariadne', args);
try {
  await writeFile(source, 'export function demo(): bigint { return 2n + 3n; }\n');
  assert.equal(cli(['eval', source, 'demo', 'bad']).status, 2);
  assert.equal(cli(['eval', source, 'missing']).status, 2);
  await writeFile(artifact, 'preserve existing output\n');
  await writeFile(source, 'export function demo(): bigint { while (true) { } return 0n; }\n');
  const extract = cli(['extract', source, '--out', artifact, '--json']);
  assert.equal(extract.status, 1, extract.stdout + extract.stderr);
  assert.equal(JSON.parse(extract.stdout).code, 'A5101');
  assert.equal(await readFile(artifact, 'utf8'), 'preserve existing output\n');
  assert.equal(cli(['extract', source, '--out', artifact, '--json', '--json']).status, 2);
  await writeFile(source, 'export function demo(): bigint { return 2n + 3n; }\n');
  assert.equal(cli(['translate', source, '--out', artifact, '--bogus', 'x']).status, 2);
  const alias = resolve(dir, 'Alias.lean');
  await symlink(source, alias);
  assert.equal(cli(['translate', source, '--out', alias]).status, 2);
  const certified = cli(['certify', source, '--out', artifact, '--namespace', 'CliTest']);
  assert.equal(certified.status, 0, certified.stdout + certified.stderr);
  const good = await readFile(artifact, 'utf8');
  assert.ok(good.includes('return 2n + 3n;'));
  await writeFile(artifact, good.replace('return 2n + 3n;', 'return 9n + 3n;'));
  const tampered = run('lake', ['env', 'lean', artifact]);
  assert.notEqual(tampered.status, 0, 'a modified source must invalidate the certificate');
  assert.ok(tampered.stdout.includes('error'), tampered.stdout + tampered.stderr);
  const falseProof = resolve(dir, 'False.lean');
  // The tactic is in scope through the import, not a trusted proof oracle.
  await writeFile(falseProof, 'import Ariadne.Kernel\nexample : (0 : Nat) = 1 := by kernel_rfl\n');
  const rejected = run('lake', ['env', 'lean', falseProof]);
  assert.notEqual(rejected.status, 0);
  assert.ok(rejected.stdout.includes('kernel'), rejected.stdout + rejected.stderr);
} finally {
  await rm(dir, { recursive: true, force: true });
}
console.log('CLI and certificate-tampering checks passed.');
