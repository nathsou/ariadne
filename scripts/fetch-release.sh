#!/usr/bin/env bash
# For a project that requires Ariadne at a release tag: download that release's build into the package's
# directory, after checking it against a SHA-256 the project pins, so `lake build` finds Ariadne built.
#
#   scripts/fetch-release.sh v0.4.0 <sha256> [.lake/packages/ariadne]
#
# The project's audit should list `Ariadne` in `replay`: every declaration of the prebuilt library is then
# re-checked by the kernel, so the archive is trusted only for the `ariadne` executable (as the pinned Lean
# toolchain is), which the hash ties to the release workflow's build of the tagged commit.
set -euo pipefail
tag=${1:?release tag}
sha=${2:?pinned sha256}
dir=${3:-.lake/packages/ariadne}
lean=$(sed 's/.*:v//' "$dir/lean-toolchain")
archive="ariadne-$tag-lean-$lean-linux-x64.tar.zst"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
curl --proto '=https' --tlsv1.2 --fail --location --retry 5 --retry-max-time 120 \
  "https://github.com/nathsou/ariadne/releases/download/$tag/$archive" -o "$tmp/$archive"
printf '%s  %s\n' "$sha" "$tmp/$archive" | sha256sum --check --strict
tar --zstd -xf "$tmp/$archive" -C "$dir"
