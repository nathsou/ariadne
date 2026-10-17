// Builds the examples' data for the page (`site/public/data/`): each example's source, its translation
// and proofs, and what Lean says about them (`lake exe extract`). Fails if a checked-in translation is
// out of date, or if Lean reports an error.
//   node data.mjs   (after `lake build Examples extract` and `lake build ariadne` in the parent)
import { execFileSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync, mkdtempSync, copyFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const repo = resolve(here, "..");
const out = join(here, "site/public/data");
const tmp = mkdtempSync(join(tmpdir(), "playground-"));
mkdirSync(out, { recursive: true });

const examples = JSON.parse(readFileSync(join(here, "examples.json"), "utf8"));
const read = (p) => readFileSync(join(repo, p), "utf8");

function extract(root, file) {
  const json = join(tmp, "info.json");
  execFileSync("lake", ["exe", "extract", json, resolve(repo, root), file], { cwd: here, stdio: ["ignore", "inherit", "inherit"] });
  return JSON.parse(readFileSync(json, "utf8"));
}

const index = [];
for (const ex of examples) {
  const started = Date.now();
  const data = { ...ex, source: read(ex.source), path: ex.source };
  if (ex.lean) {
    const umbrellaPath = join(ex.lean.root, ex.lean.file);
    const leanPath = ex.lean.split ? umbrellaPath.replace(/\.lean$/, "/Model.lean") : umbrellaPath;
    // The translation is checked in; it must be what the translator gives now.
    const fresh = join(tmp, "fresh.lean");
    execFileSync(join(repo, ".lake/build/bin/ariadne"),
      ["translate", ex.source, "--out", fresh, "--namespace", ex.namespace, ...(ex.lean.split ? ["--split"] : [])], { cwd: repo });
    const files = [[fresh, umbrellaPath]];
    if (ex.lean.split) {
      for (const part of ["Model", "Certificate"]) {
        files.push([fresh.replace(/\.lean$/, `/${part}.lean`), umbrellaPath.replace(/\.lean$/, `/${part}.lean`)]);
      }
    }
    for (const [generated, checkedIn] of files) {
      if (readFileSync(generated, "utf8") !== read(checkedIn)) {
        throw new Error(`${checkedIn} is out of date: run node scripts/regenerate.mjs`);
      }
    }
    const info = extract(ex.lean.root, ex.lean.split ? ex.lean.file.replace(/\.lean$/, "/Model.lean") : ex.lean.file);
    // The generated file's own proofs are `decide` steps and structural equations: keep its hovers, and
    // of its theorems the ones a user cites (the source theorems and the frame lemmas).
    info.goals = [];
    info.theorems = info.theorems.filter((t) => /\.(source|keeps\.[^.]+)$/.test(t.name));
    data.lean = { path: leanPath, text: read(leanPath), info };
  }
  if (ex.proofs) {
    const proofsPath = join(ex.proofs.root, ex.proofs.file);
    data.proofs = { path: proofsPath, text: read(proofsPath), info: extract(ex.proofs.root, ex.proofs.file) };
  }
  writeFileSync(join(out, `${ex.slug}.json`), JSON.stringify(data));
  const { lean, proofs, ...meta } = ex;
  index.push({ ...meta, theorems: data.proofs?.info.theorems.length ?? 0, lines: data.source.split("\n").length });
  console.log(`${ex.slug}: ${((Date.now() - started) / 1000).toFixed(1)}s`);
}
writeFileSync(join(out, "examples.json"), JSON.stringify(index));
copyFileSync(join(repo, "docs/LANGUAGE.md"), join(out, "LANGUAGE.md"));
const version = readFileSync(join(repo, "lakefile.toml"), "utf8").match(/^version = "(.*)"/m)[1];
let commit = "";
try { commit = execFileSync("git", ["rev-parse", "HEAD"], { cwd: repo, encoding: "utf8" }).trim(); } catch {}
writeFileSync(join(out, "build.json"), JSON.stringify({ version, commit, lean: read("lean-toolchain").trim() }));
