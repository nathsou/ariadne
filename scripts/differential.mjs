// Test-only harness. Runs with Bun or Node >=24; no npm packages are required.
import { readdir } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import assert from 'node:assert/strict';

const cli = resolve('.lake/build/bin/ariadne');
function observe(value) {
  if (value === undefined) return ['undefined'];
  if (value === null) return ['null'];
  switch (typeof value) {
    case 'number': {
      // NaN payloads are unobservable in the subset. Normalize to the model's NaN.
      const bytes = new DataView(new ArrayBuffer(8));
      bytes.setFloat64(0, Number.isNaN(value) ? NaN : value);
      return ['number', bytes.getBigUint64(0).toString()];
    }
    case 'bigint': return ['bigint', value.toString()];
    case 'boolean': return ['boolean', value];
    case 'string': return ['string', Array.from({ length: value.length }, (_, i) => value.charCodeAt(i))];
    case 'object':
      if (Array.isArray(value)) return ['array', value.map(observe)];
      if (value instanceof Map) return ['map', [...value].map(([k, v]) => [observe(k), observe(v)])];
      return ['record', Object.entries(value).map(([k, v]) => [k, observe(v)])];
    default: throw new Error(`Unsupported observation: ${typeof value}`);
  }
}

let count = 0;
for (const file of (await readdir('examples')).filter(f => f.endsWith('.ts')).sort()) {
  const path = resolve('examples', file);
  const module = await import(pathToFileURL(path).href);
  for (const [name, fn] of Object.entries(module)) {
    if (typeof fn !== 'function' || fn.length !== 0 || name === 'diverges') continue;
    const result = spawnSync(cli, ['eval', path, name], { encoding: 'utf8', timeout: 30000 });
    assert.equal(result.status, 0, `${file}:${name}: ${result.stderr}\n${result.stdout}`);
    assert.deepEqual(JSON.parse(result.stdout), { ok: observe(fn()) }, `${file}:${name}`);
    count++;
  }
}
console.log(`Differential execution passed: ${count} entries.`);
