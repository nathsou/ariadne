#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# CI restores the prepare job's build before invoking individual phases.
# Local invocation runs the same phases in sequence.
phase=${1:-all}
if (( $# > 1 )) || [[ ! "$phase" =~ ^(all|prepare|tests|operational|shallow|shallow-data|shallow-values|verify|verify-basic|verify-data|verify-source)$ ]]; then
  echo "Usage: scripts/check.sh [all|prepare|tests|operational|shallow|shallow-data|shallow-values|verify|verify-basic|verify-data|verify-source]" >&2
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
  lake build ariadne Ariadne
  scripts/regenerate.sh
  git diff --exit-code -- Examples/Generated Examples/Compiled Examples/OperationalReference Examples/ShallowReference Examples/Shallow Examples/Tamper
}

run_tests() {
  for source in Tests/*.lean; do
    stem=$(basename "$source" .lean)
    lake build "Tests.$stem"
  done
  lake build Tests
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

run_shallow_data() {
  for source in examples/reference/*.ts; do
    stem=$(basename "$source" .ts)
    lake build "Examples.ShallowReference.$stem"
  done
  for source in examples/shallow/*.ts; do
    stem=$(basename "$source" .ts)
    case "$stem" in
      arrays|collections|loops|unions|records|entryguards) lake build "Examples.Shallow.$stem" ;;
    esac
  done
}

run_shallow_values() {
  for source in examples/shallow/*.ts; do
    stem=$(basename "$source" .ts)
    # Every other file, including future fixtures, belongs to this group.
    case "$stem" in
      arrays|collections|loops|unions|records|entryguards) ;;
      *) lake build "Examples.Shallow.$stem" ;;
    esac
  done
  lake build Examples.ClassAdequacy
  lake build Examples.ClassConstructionAdequacy
  lake build Examples.ReferenceSource.Registers
  for source in examples/tamper/*.ts; do
    stem=$(basename "$source" .ts)
    lake build "Examples.Tamper.$stem"
  done
}

run_shallow() {
  run_shallow_data
  run_shallow_values
}

select_js() {
  if command -v bun >/dev/null 2>&1; then
    js=bun
  else
    js=node
  fi
}

run_verify_basic() {
  lake build Tests Examples
  lake env lean scripts/Audit.lean
  select_js
  timed scripts/differential.mjs "$js" scripts/differential.mjs
  timed scripts/generated-cases.mjs "$js" scripts/generated-cases.mjs
  timed scripts/negative.mjs "$js" scripts/negative.mjs
  timed scripts/realm.mjs "$js" scripts/realm.mjs
  timed scripts/compiler.mjs "$js" scripts/compiler.mjs
  timed scripts/reference.mjs "$js" scripts/reference.mjs
  timed scripts/reference-operational.mjs "$js" scripts/reference-operational.mjs
  timed scripts/builtins.mjs "$js" scripts/builtins.mjs
}

run_verify_source() {
  select_js
  timed scripts/cli.mjs "$js" scripts/cli.mjs
  timed scripts/shallow.mjs "$js" scripts/shallow.mjs
  timed scripts/source-transfer.mjs "$js" scripts/source-transfer.mjs
  timed scripts/shared-source.mjs "$js" scripts/shared-source.mjs
  timed scripts/guarded-shared-source.mjs "$js" scripts/guarded-shared-source.mjs
  timed scripts/int53-source-transfer.mjs "$js" scripts/int53-source-transfer.mjs
}

run_verify_data() {
  select_js
  timed scripts/entry-guards.mjs "$js" scripts/entry-guards.mjs
  timed scripts/shallow-arrays.mjs "$js" scripts/shallow-arrays.mjs
  timed scripts/shallow-optionals.mjs "$js" scripts/shallow-optionals.mjs
  timed scripts/shallow-loops.mjs "$js" scripts/shallow-loops.mjs
  timed scripts/shallow-collections.mjs "$js" scripts/shallow-collections.mjs
  timed scripts/shallow-records.mjs "$js" scripts/shallow-records.mjs
  timed scripts/shallow-unions.mjs "$js" scripts/shallow-unions.mjs
  timed scripts/shallow-state.mjs "$js" scripts/shallow-state.mjs
  timed scripts/shallow-projections.mjs "$js" scripts/shallow-projections.mjs
  timed scripts/shallow-simultaneous.mjs "$js" scripts/shallow-simultaneous.mjs
  timed scripts/shallow-classes.mjs "$js" scripts/shallow-classes.mjs
  timed scripts/shallow-int53.mjs "$js" scripts/shallow-int53.mjs
  timed scripts/reference-shallow.mjs "$js" scripts/reference-shallow.mjs
}

run_verify() {
  run_verify_basic
  run_verify_data
  run_verify_source
}

case "$phase" in
  all)
    timed prepare run_prepare
    timed tests run_tests
    timed operational run_operational
    timed shallow run_shallow
    timed verify run_verify
    ;;
  shallow-data) timed "$phase" run_shallow_data ;;
  shallow-values) timed "$phase" run_shallow_values ;;
  verify-basic) timed "$phase" run_verify_basic ;;
  verify-data) timed "$phase" run_verify_data ;;
  verify-source) timed "$phase" run_verify_source ;;
  *) timed "$phase" "run_$phase" ;;
esac
