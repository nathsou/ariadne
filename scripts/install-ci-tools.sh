#!/usr/bin/env bash
set -euo pipefail
# Ubuntu x86_64 CI only. Verify every executable archive before unpacking it.
# Version updates must change both the URL and the reviewed hash.
tool_dir="${RUNNER_TEMP:?}/ariadne-tools"
mkdir -p "$tool_dir"
cd "$tool_dir"
fetch() {
  # Release downloads occasionally return a cached HTTP 500 for several seconds.
  # Allow the transient response to expire; checksum failures still stop here.
  curl --proto '=https' --tlsv1.2 --fail --location --connect-timeout 20 \
    --retry 6 --retry-max-time 120 "$1" -o "$2"
  printf '%s  %s\n' "$3" "$2" | sha256sum --check --strict
}
fetch https://releases.lean-lang.org/lean4/v4.35.0/lean-4.35.0-linux.tar.zst lean.tar.zst 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d
fetch https://github.com/oven-sh/bun/releases/download/bun-v1.4.3/bun-linux-x64.zip bun.zip 3e730528d89775f03f87f05c06787c4df4099d0a37f3f252e7b829cb23816e18
tar --zstd -xf lean.tar.zst
unzip -q bun.zip
# The only tools: checksum-pinned Lean (with Lake) and Bun. No toolchain manager.
printf '%s\n' "$tool_dir/lean-4.35.0-linux/bin" "$tool_dir/bun-linux-x64" >> "${GITHUB_PATH:?}"
