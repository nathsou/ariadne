#!/usr/bin/env bash
# All checks: the general theorem, regenerated fixtures (kernel-checked),
# the model against JavaScript (cases, differential execution, random programs),
# negative fixtures, and the parser against the TypeScript compiler.
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
git diff --exit-code -- Tests/Generated
lake build Tests
lake exe audit

"$js" scripts/differential.mjs
"$js" scripts/negative.mjs
"$js" scripts/fuzz-model.mjs

# The TypeScript compiler, pinned by bun.lock (with its integrity hash), for the parser cross-check.
if [ "$js" = bun ]; then
  bun install --frozen-lockfile --silent
  bun scripts/crosscheck.mjs
else
  echo "Parser cross-check skipped: it needs Bun (bun.lock pins the TypeScript compiler)."
fi
