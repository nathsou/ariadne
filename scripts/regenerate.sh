#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p Examples/Generated
for source in examples/*.ts; do
  stem=$(basename "$source" .ts)
  namespace="Example_${stem}"
  .lake/build/bin/ariadne translate "$source" --out "Examples/Generated/${stem}.lean" --namespace "$namespace"
done
