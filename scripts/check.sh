#!/usr/bin/env bash
# All checks: the general theorem, regenerated fixtures (kernel-checked),
# the model against JavaScript (cases, differential execution, random programs),
# negative fixtures, the boundary validators, and the parser against the TypeScript compiler.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build Ariadne ariadne

if command -v bun >/dev/null 2>&1; then js=bun; else js=node; fi
"$js" scripts/model.mjs

"$js" scripts/regenerate.mjs
git diff --exit-code -- Tests/Generated examples/quickstart/Quickstart playground/Examples
if [ -n "$(git ls-files --others --exclude-standard -- Tests/Generated examples/quickstart/Quickstart playground/Examples)" ]; then
  echo "Regeneration produced untracked files; check in every model and certificate."
  exit 1
fi
lake build Tests
"$js" scripts/emission.mjs
lake exe audit
(cd playground && lake build Examples)
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
