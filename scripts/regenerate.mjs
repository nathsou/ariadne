// One source of truth for every checked-in translation, including the playground.
import { readdirSync, readFileSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../", import.meta.url));
function translate(source, out, namespace, split = false) {
  execFileSync(`${root}.lake/build/bin/ariadne`,
    ["translate", source, "--out", out, "--namespace", namespace, ...(split ? ["--split"] : [])],
    { cwd: root, stdio: "inherit" });
}

for (const file of readdirSync(`${root}Tests/fixtures`).filter(f => f.endsWith(".ts")).sort()) {
  const module = file.slice(0, -3).replace(/(^|-)([a-z])/g, (_, __, c) => c.toUpperCase());
  translate(`Tests/fixtures/${file}`, `Tests/Generated/${module}.lean`, `Tests.Generated.${module}`, true);
}
translate("examples/quickstart/src/ledger.ts", "examples/quickstart/Quickstart/Ledger.lean", "Quickstart.Ledger", true);
for (const example of JSON.parse(readFileSync(`${root}playground/examples.json`, "utf8"))) {
  if (example.lean && !example.lean.split) translate(example.source, `${example.lean.root}/${example.lean.file}`, example.namespace);
}
