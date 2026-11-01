#!/usr/bin/env bash
# Builds the no-timer kernel + dom0 exactly as `NO_TIMER=1 boot/run.sh` does and stores the boot image
# (aloader + jumbo initrd = kernel ELF followed by dom0 ELF) in OUT_DIR, default boot/bench/out/image,
# with built-from.txt naming the commit, the dirty src/ and boot/ files, and the image hashes.
# WORKTREE builds another checkout instead of this one, such as a `git worktree add` of a baseline
# commit for an A/B comparison.
# Usage: [WORKTREE=<checkout>] build-parallel-call-image.sh [out_dir]
set -euo pipefail
BENCH=$(realpath "$(dirname "$0")")
WT=$(realpath "${WORKTREE:-$BENCH/../..}")
mkdir -p "${1:-$BENCH/out/image}"; OUT_DIR=$(realpath "${1:-$BENCH/out/image}")
cd "$WT/boot"
cargo +1.99.1 build --profile release -p aloader -p kernel -p dom0 --features kernel/no-timer,dom0/no-timer
OUT=target/x86_64-unknown-none/release
cp "$OUT/aloader" "$OUT_DIR/aloader"
cat "$OUT/kernel" "$OUT/dom0" > "$OUT_DIR/jumbo"
git -C "$WT" log -1 --format='%H %s' > "$OUT_DIR/built-from.txt"
git -C "$WT" status --short -- src boot >> "$OUT_DIR/built-from.txt"
sha256sum "$OUT_DIR/aloader" "$OUT_DIR/jumbo" >> "$OUT_DIR/built-from.txt"
