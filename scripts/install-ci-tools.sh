#!/usr/bin/env bash
set -euo pipefail
# Ubuntu x86_64 CI only. Verify every executable archive before unpacking it.
# Version updates must change both the URL and the reviewed hash.
tool_dir="${RUNNER_TEMP:?}/ariadne-tools"
mkdir -p "$tool_dir"
cd "$tool_dir"
fetch() {
  curl --proto '=https' --tlsv1.2 --fail --location --retry 3 "$1" -o "$2"
  printf '%s  %s\n' "$3" "$2" | sha256sum --check --strict
}
fetch https://github.com/leanprover/elan/releases/download/v4.1.2/elan-x86_64-unknown-linux-gnu.tar.gz elan.tar.gz f81c2e48c1588d4612cd2c8851947898a45ac8d72748a07dff3a5694f1cf589b
fetch https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst lean.tar.zst 47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4
fetch https://github.com/oven-sh/bun/releases/download/bun-v1.3.5/bun-linux-x64.zip bun.zip 7051d86a924aefea3e0b96213b5fd8f79c0793f9cae6534233e627e5c3db4669
tar -xzf elan.tar.gz
./elan-init -y --no-modify-path --default-toolchain none
tar --zstd -xf lean.tar.zst
unzip -q bun.zip
# Put the verified binaries first; elan must not fetch an unchecked toolchain.
printf '%s\n' "$tool_dir/lean-4.34.1-linux/bin" "$tool_dir/bun-linux-x64" >> "${GITHUB_PATH:?}"
