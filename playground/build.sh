#!/usr/bin/env bash
# Builds the playground into playground/site/dist (a static site), from a checkout with Lean (the
# pinned toolchain), Bun, CMake and Emscripten's emcc on PATH. CI runs it (.github/workflows/pages.yml).
#   1. Ariadne's translator and the examples, with their proofs, checked by Lean's kernel;
#   2. the translator compiled to WebAssembly (wasm/build.sh);
#   3. what Lean says about the examples, for the page (data.mjs);
#   4. the page itself (site/).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/.."
lake build ariadne
(cd playground && lake build Examples extract Web)
bash playground/wasm/build.sh
(cd playground && bun data.mjs)
cd playground/site
bun install --frozen-lockfile
bun run check
bun run build
