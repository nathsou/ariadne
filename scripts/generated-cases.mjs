// Deterministic, generated differential cases. This is test code, not a runtime dependency.
import { mkdir, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import assert from 'node:assert/strict';

const dir = resolve('work/generated-cases');
await mkdir(dir, { recursive: true });
let seed = 0x51c0ffee;
const next = () => { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed; };
let count = 0;
try {
  for (let i = 0; i < 64; i++) {
    const a = BigInt(next() % 2001) - 1000n;
    const b = BigInt(next() % 999) + 1n;
    const limit = next() % 20;
    const file = resolve(dir, `case${i}.ts`);
    const source = `export function demo(): bigint {
  let a = ${a}n;
  let b = ${b}n;
  for (let i = 0; i < ${limit}; i++) {
    if (i % 3 === 0) { a += b; continue; }
    a = (a * 3n - b) % 1000000007n;
    b = b / 2n + 1n;
  }
  const xs = [a, b, a % b];
  const ys = xs.map((x: bigint) => x * x);
  return ys.reduce((acc: bigint, x: bigint) => acc + x, 0n);
}
`;
    await writeFile(file, source);
    const native = (await import(pathToFileURL(file).href)).demo();
    const modeled = spawnSync('.lake/build/bin/ariadne', ['eval', file, 'demo'], {
      encoding: 'utf8', timeout: 10000,
    });
    assert.equal(modeled.status, 0, `seed ${seed}: ${modeled.stderr}`);
    assert.deepEqual(JSON.parse(modeled.stdout), { ok: ['bigint', native.toString()] }, `case ${i}`);
    count++;
  }
} finally {
  await rm(dir, { recursive: true, force: true });
}
console.log(`Generated differential execution passed: ${count} programs.`);
