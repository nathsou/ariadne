// Both layouts must check, and a certificate must reject a changed body or safety condition.
import assert from "node:assert/strict";
import { execFileSync, spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, delimiter } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../", import.meta.url));
const temporary = mkdtempSync(join(tmpdir(), "ariadne-emission-"));
const inheritedPath = execFileSync("lake", ["env", "printenv", "LEAN_PATH"], { cwd: root, encoding: "utf8" }).trim();
const env = { ...process.env, LEAN_PATH: temporary + delimiter + inheritedPath };
function lean(file, output) {
  return spawnSync("lean", [...(output ? ["-o", output] : []), file],
    { cwd: temporary, env, encoding: "utf8" });
}
function checks(file, output) {
  const run = lean(file, output);
  assert.equal(run.status, 0, run.stdout + run.stderr);
}
const cli = `${root}.lake/build/bin/ariadne`;
try {
  const source = `${root}Tests/fixtures/emission.ts`;
  execFileSync(cli, ["translate", source, "--out", join(temporary, "Regression.lean"),
    "--namespace", "Regression", "--split"]);
  const modelPath = join(temporary, "Regression/Model.lean");
  const original = readFileSync(modelPath, "utf8");
  assert(!original.includes("noncomputable def ast"));
  assert(!original.includes("noncomputable def typed"));
  checks("Regression/Model.lean", "Regression/Model.olean");
  checks("Regression/Certificate.lean", "Regression/Certificate.olean");
  checks("Regression.lean");
  execFileSync(cli, ["translate", source, "--out", join(temporary, "Standalone.lean"),
    "--namespace", "Standalone"]);
  checks("Standalone.lean");

  const changes = [
    ["body", original.replace("Int.fdiv (lo + hi)", "Int.fdiv (lo - hi)")],
    ["safety", original.replace(/  Ariadne\.inRange \(lo \+ hi\) && .*\n/, "  true\n")],
  ];
  for (const [kind, changed] of changes) {
    assert.notEqual(changed, original, `${kind} mutation did not apply`);
    writeFileSync(modelPath, changed);
    checks("Regression/Model.lean", "Regression/Model.olean");
    const rejected = lean("Regression/Certificate.lean");
    assert.notEqual(rejected.status, 0, `certificate accepted a changed ${kind}`);
    assert.match(rejected.stdout + rejected.stderr, /kernel_rfl|type mismatch|not definitionally equal/i);
  }
  console.log("Emission: both layouts check; changed bodies and safety conditions are rejected.");
} finally {
  rmSync(temporary, { recursive: true, force: true });
}
