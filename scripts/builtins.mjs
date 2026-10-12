// Deterministic binary64 edge/random coverage of the executable decimal model.
import { mkdir, mkdtemp, writeFile, rm } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { resolve } from 'node:path';
import assert from 'node:assert/strict';

const bits = [];
const view = new DataView(new ArrayBuffer(8));
for (const value of [0, -0, NaN, Infinity, -Infinity, Number.MIN_VALUE, Number.MAX_VALUE,
  Number.MIN_SAFE_INTEGER, Number.MAX_SAFE_INTEGER, 1000000000000000128,
  0.1, 1e-7, 1e-6, 1e-5, 1e20, 1e21, 1e22, 1.2345678901234567]) {
  view.setFloat64(0, value);
  bits.push(view.getBigUint64(0));
}
for (let exponent = -324; exponent <= 308; exponent++) {
  view.setFloat64(0, Number(`1e${exponent}`));
  const value = view.getBigUint64(0);
  bits.push(value, value + 1n);
  if (value > 0n) bits.push(value - 1n);
}
let seed = 0x123456789abcdefn;
for (let i = 0; i < 512; i++) {
  seed = BigInt.asUintN(64, seed * 6364136223846793005n + 1442695040888963407n);
  bits.push(seed);
}
const expected = bits.map(value => {
  view.setBigUint64(0, value);
  return String(view.getFloat64(0));
});
await mkdir('work', { recursive: true });
const dir = await mkdtemp(resolve('work/builtins-'));
try {
  const path = resolve(dir, 'Decimal.lean');
  const chunks = [];
  for (let i = 0; i < bits.length; i += 128) chunks.push(bits.slice(i, i + 128));
  await writeFile(path, 'import Ariadne.Builtins\nimport Lean\n' +
    'set_option maxRecDepth 4096\nset_option maxHeartbeats 0\n' +
    'def render (bits : Nat) : Lean.Json := .str (String.ofList ((Ariadne.Builtins.numberString (Float.Model.ofBits (UInt64.ofNat bits))).map (fun u => Char.ofNat u.toNat)))\n' +
    chunks.map(xs => `#eval IO.println ((Lean.Json.arr (#[${xs}].map render)).compress)\n`).join(''));
  const result = spawnSync('lake', ['env', 'lean', path], {
    encoding: 'utf8', timeout: 120000, maxBuffer: 8e6,
  });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.deepEqual(result.stdout.trim().split('\n').flatMap(JSON.parse), expected);
  console.log(`Decimal formatting passed: ${bits.length} binary64 values, including decimal boundaries and adjacent floats.`);
} finally {
  await rm(dir, { recursive: true, force: true });
}
