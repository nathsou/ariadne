import { readdir, readFile } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import assert from 'node:assert/strict';

let count = 0;
for (const file of (await readdir('examples/negative')).filter(f => f.endsWith('.ts')).sort()) {
  const path = `examples/negative/${file}`;
  const source = await readFile(path, 'utf8');
  const expected = source.match(/^\/\/ expected: (A\d+)/)[1];
  const result = spawnSync('.lake/build/bin/ariadne', ['check', path, '--json'], {
    encoding: 'utf8', timeout: 10000,
  });
  assert.equal(result.status, 1, `${file}: expected rejection, got ${result.stdout}`);
  const diagnostic = JSON.parse(result.stdout);
  assert.equal(diagnostic.code, expected, file);
  assert.equal(diagnostic.schemaVersion, 1, file);
  assert.equal(diagnostic.severity, 'error', file);
  assert.ok(diagnostic.message.length > 0, file);
  count++;
}
console.log(`Negative diagnostics passed: ${count} fixtures.`);
