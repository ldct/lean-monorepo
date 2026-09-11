#!/usr/bin/env bash
# Build optimized Lean on Apple Silicon and download the standard Mathlib cache.
set -euo pipefail
cd "$(dirname "$0")/.."
project=$PWD
jobs=${JOBS:-12}
base=819816b2e0a3bf405af45ae5c7af2491d8f5bee6
release=d06e784fc4e9e031ea4db91d706edbcef287a141
sources=$project/.lake/toolchains
lean=$sources/lean4
upstream=$sources/lean-optimizations
mkdir -p "$sources"
if [[ ! -d "$upstream/.git" ]]; then
  git clone https://github.com/danromik/lean-optimizations "$upstream"
  git -C "$upstream" checkout "$release"
fi
[[ $(git -C "$upstream" rev-parse HEAD) == "$release" ]]
if [[ ! -d "$lean/.git" ]]; then
  git clone --depth 1 --branch v4.33.1 https://github.com/leanprover/lean4 "$lean"
fi
[[ $(git -C "$lean" rev-parse HEAD) == "$base" ]]
for patch in lean4-v4.33.1-optimized.patch fix-codegen-meta-initialize.patch; do
  if git -C "$lean" apply --reverse --check "$upstream/patches/$patch" 2>/dev/null; then
    continue
  fi
  git -C "$lean" apply --binary "$upstream/patches/$patch"
done
(
  cd "$lean"
  cmake --preset release -DLEAN_GITHASH_OVERRIDE="$base" \
    -DLEAN_PLATFORM_TARGET=arm64-apple-darwin24.6.0
  cmake --build --preset release -- -j"$jobs"
  cmake --build --preset release --target stage2 -- -j"$jobs"
)
# Fetch under the stock toolchain name: Mathlib's cache validates that file literally.
# This compiles at most the cache-fetching helper, never the Mathlib library.
printf '%s\n' leanprover/lean4:v4.33.1 > lean-toolchain
MATHLIB_NO_CACHE_ON_UPDATE=1 lake --keep-toolchain update
lake exe cache get
elan toolchain link lean-v4.33.1-optimized "$lean/build/release/stage2"
printf '%s\n' lean-v4.33.1-optimized > lean-toolchain
python3 scripts/install-wrapper.py
# Fail rather than silently rebuild Mathlib if its downloaded cache is incomplete.
lake --no-build build Mathlib
lake build
lake env lean Playground/Scratch.lean
# Warm lazy/search caches before writing the image keyed on them.
lake env lean scripts/Exact.lean
LEAN_TACTIC_INDEX_WRITE=1 lake env lean scripts/Import.lean
