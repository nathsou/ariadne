#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# CI restores the prepare job's build before invoking individual phases.
# Local invocation runs the same phases in sequence.
phase=${1:-all}
if (( $# > 1 )) || [[ ! "$phase" =~ ^(all|prepare|operational|shallow|verify)$ ]]; then
  echo "Usage: scripts/check.sh [all|prepare|operational|shallow|verify]" >&2
  exit 2
fi

timed() {
  local label=$1
  shift
  local started=$SECONDS
  "$@"
  printf 'Timing: %s: %ss\n' "$label" "$((SECONDS - started))"
}

run_prepare() {
  lake build ariadne Tests Ariadne
  scripts/regenerate.sh
  git diff --exit-code -- Examples/Generated Examples/Compiled Examples/OperationalReference Examples/ShallowReference Examples/Shallow Examples/Tamper
}

run_operational() {
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
}

run_shallow() {
  for source in examples/reference/*.ts; do
    stem=$(basename "$source" .ts)
    lake build "Examples.ShallowReference.$stem"
  done
  for source in examples/shallow/*.ts; do
    stem=$(basename "$source" .ts)
    lake build "Examples.Shallow.$stem"
  done
  for source in examples/tamper/*.ts; do
    stem=$(basename "$source" .ts)
    lake build "Examples.Tamper.$stem"
  done
}

run_verify() {
  lake build Examples
  lake env lean scripts/Audit.lean

  if command -v bun >/dev/null 2>&1; then
    js=bun
  else
    js=node
  fi
  timed scripts/differential.mjs "$js" scripts/differential.mjs
  timed scripts/generated-cases.mjs "$js" scripts/generated-cases.mjs
  timed scripts/negative.mjs "$js" scripts/negative.mjs
  timed scripts/realm.mjs "$js" scripts/realm.mjs
  timed scripts/cli.mjs "$js" scripts/cli.mjs
  timed scripts/compiler.mjs "$js" scripts/compiler.mjs
  timed scripts/reference.mjs "$js" scripts/reference.mjs
  timed scripts/reference-operational.mjs "$js" scripts/reference-operational.mjs
  timed scripts/shallow.mjs "$js" scripts/shallow.mjs
  timed scripts/source-transfer.mjs "$js" scripts/source-transfer.mjs
  timed scripts/int53-source-transfer.mjs "$js" scripts/int53-source-transfer.mjs
  timed scripts/shallow-arrays.mjs "$js" scripts/shallow-arrays.mjs
  timed scripts/shallow-loops.mjs "$js" scripts/shallow-loops.mjs
  timed scripts/shallow-collections.mjs "$js" scripts/shallow-collections.mjs
  timed scripts/shallow-records.mjs "$js" scripts/shallow-records.mjs
  timed scripts/shallow-unions.mjs "$js" scripts/shallow-unions.mjs
  timed scripts/shallow-state.mjs "$js" scripts/shallow-state.mjs
  timed scripts/shallow-classes.mjs "$js" scripts/shallow-classes.mjs
  timed scripts/shallow-int53.mjs "$js" scripts/shallow-int53.mjs
  timed scripts/reference-shallow.mjs "$js" scripts/reference-shallow.mjs
  timed scripts/builtins.mjs "$js" scripts/builtins.mjs
}

case "$phase" in
  all)
    timed prepare run_prepare
    timed operational run_operational
    timed shallow run_shallow
    timed verify run_verify
    ;;
  *) timed "$phase" "run_$phase" ;;
esac
