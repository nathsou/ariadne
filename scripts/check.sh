#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

lake build ariadne Tests Ariadne
scripts/regenerate.sh
git diff --exit-code -- Examples/Generated Examples/Compiled Examples/OperationalReference Examples/Shallow
# Kernel computation is memory intensive. Compile independent certificates serially.
for source in examples/*.ts; do
  stem=$(basename "$source" .ts)
  lake build "Examples.Generated.$stem"
done
for source in examples/reference/*.ts; do
  stem=$(basename "$source" .ts)
  lake build "Examples.OperationalReference.$stem"
done
for source in examples/scalar/*.ts; do
  stem=$(basename "$source" .ts)
  lake build "Examples.Compiled.$stem"
done
for source in examples/shallow/*.ts; do
  stem=$(basename "$source" .ts)
  lake build "Examples.Shallow.$stem"
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
"$js" scripts/compiler.mjs
"$js" scripts/reference.mjs
"$js" scripts/reference-operational.mjs
"$js" scripts/shallow.mjs
"$js" scripts/shallow-arrays.mjs
"$js" scripts/shallow-loops.mjs
"$js" scripts/shallow-collections.mjs
"$js" scripts/shallow-records.mjs
"$js" scripts/shallow-unions.mjs
"$js" scripts/builtins.mjs
