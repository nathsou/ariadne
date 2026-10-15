// The modules `Web` imports, transitively: `node closure.mjs ROOT...` with LEAN_SRC_PATH roots,
// one per line. Lake builds their C; the stdlib's is generated from the toolchain's sources.
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

const roots = process.env.LEAN_SRC_PATH.split(":");
const find = (m) => roots.map((r) => join(r, ...m.split(".")) + ".lean").find(existsSync);
const seen = new Set();
const stack = process.argv.slice(2);
while (stack.length) {
  const m = stack.pop();
  if (seen.has(m)) continue;
  seen.add(m);
  const path = find(m);
  if (!path) throw new Error(`no source for ${m}`);
  const src = readFileSync(path, "utf8");
  for (const [, im] of src.matchAll(/^(?:public\s+|meta\s+)*import\s+(?:all\s+)?([\w.]+)/gm)) stack.push(im);
  if (!/^\s*prelude\b/m.test(src)) stack.push("Init");
}
console.log([...seen].sort().join("\n"));
