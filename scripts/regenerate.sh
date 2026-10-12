#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p Examples/Generated
for source in examples/*.ts; do
  stem=$(basename "$source" .ts)
  namespace="Example_${stem}"
  .lake/build/bin/ariadne translate "$source" --out "Examples/Generated/${stem}.lean" --namespace "$namespace"
done
mkdir -p Examples/OperationalReference
for source in examples/reference/*.ts; do
  stem=$(basename "$source" .ts)
  .lake/build/bin/ariadne translate "$source" \
    --out "Examples/OperationalReference/${stem}.lean" --namespace "Reference_${stem}"
done
mkdir -p Examples/Compiled
for source in examples/scalar/*.ts; do
  stem=$(basename "$source" .ts)
  .lake/build/bin/ariadne compile "$source" "$stem" \
    --out "Examples/Compiled/${stem}.lean" --namespace "Compiled_${stem}"
done
