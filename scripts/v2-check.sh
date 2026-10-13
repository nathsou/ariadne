#!/usr/bin/env bash
# Checks for Ariadne v2: the general theorem, regenerated fixtures (kernel-checked),
# differential execution against JavaScript, and negative fixtures.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build V2 ariadne2

for source in V2Tests/fixtures/*.ts; do
  stem=$(basename "$source" .ts)
  module=$(echo "$stem" | sed -E 's/(^|-)([a-z0-9])/\U\2/g')
  .lake/build/bin/ariadne2 translate "$source" --out "V2Tests/Generated/$module.lean" \
    --namespace "V2Tests.Generated.$module"
done
git diff --exit-code -- V2Tests/Generated
lake build V2Tests
lake env lean scripts/V2Audit.lean

if command -v bun >/dev/null 2>&1; then js=bun; else js=node; fi
"$js" scripts/v2-differential.mjs
"$js" scripts/v2-negative.mjs
