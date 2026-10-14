#!/usr/bin/env bash
# All checks: the general theorem, regenerated fixtures (kernel-checked),
# the model against JavaScript (cases, differential execution, random programs),
# negative fixtures, the boundary validators, and the parser against the TypeScript compiler.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build Ariadne ariadne

if command -v bun >/dev/null 2>&1; then js=bun; else js=node; fi
"$js" scripts/model.mjs

for source in Tests/fixtures/*.ts; do
  stem=$(basename "$source" .ts)
  module=$(echo "$stem" | sed -E 's/(^|-)([a-z0-9])/\U\2/g')
  .lake/build/bin/ariadne translate "$source" --out "Tests/Generated/$module.lean" \
    --namespace "Tests.Generated.$module"
done
.lake/build/bin/ariadne translate examples/quickstart/src/ledger.ts --out examples/quickstart/Quickstart/Ledger.lean \
  --namespace Quickstart.Ledger
git diff --exit-code -- Tests/Generated examples/quickstart/Quickstart
lake build Tests
lake exe audit
# The quickstart example, built and audited as a project depending on Ariadne.
(cd examples/quickstart && lake build Quickstart audit && lake exe audit)

"$js" scripts/differential.mjs
# The same calls on the fixtures as a production build emits them (bundled, minified).
if [ "$js" = bun ]; then
  compiled=$(mktemp -d)
  bun build Tests/fixtures/*.ts --root Tests/fixtures --outdir "$compiled" --target browser --format esm --minify >/dev/null
  bun scripts/differential.mjs Tests/fixtures 300 "$compiled"
  rm -rf "$compiled"
fi
"$js" scripts/negative.mjs
"$js" scripts/fuzz-model.mjs
"$js" scripts/validators.mjs

# The TypeScript compiler, pinned by bun.lock (with its integrity hash), for the parser cross-check.
if [ "$js" = bun ]; then
  bun install --frozen-lockfile --silent
  bun scripts/crosscheck.mjs
else
  echo "Parser cross-check skipped: it needs Bun (bun.lock pins the TypeScript compiler)."
fi
