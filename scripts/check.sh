#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

lake build ariadne Tests Ariadne
scripts/regenerate.sh
git diff --exit-code -- Examples/Generated
# Kernel computation is memory intensive. Compile independent certificates serially.
for source in examples/*.ts; do
  stem=$(basename "$source" .ts)
  lake build "Examples.Generated.$stem"
done
lake build Examples
lake env lean scripts/Audit.lean

if command -v bun >/dev/null 2>&1; then
  js=bun
else
  js=node
fi
"$js" scripts/differential.mjs
"$js" scripts/generated-cases.mjs
"$js" scripts/negative.mjs
"$js" scripts/realm.mjs
"$js" scripts/cli.mjs
