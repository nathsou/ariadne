#!/usr/bin/env bash
# All checks: the general theorem, regenerated fixtures (kernel-checked),
# the model against JavaScript, differential execution, and negative fixtures.
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
