#!/usr/bin/env bash
# Builds the no-timer kernel + dom0 exactly as `NO_TIMER=1 boot/run.sh` does and stores the boot image
# (aloader + jumbo initrd = kernel ELF followed by dom0 ELF) in OUT_DIR, default boot/bench/out/image,
# with built-from.txt naming the commit, the dirty src/ and boot/ files, the parallel timings, and the
# image hashes.
# WORKTREE builds another checkout instead of this one, such as a `git worktree add` of a baseline
# commit for an A/B comparison, or an exported snapshot (no git metadata needed).
# PARALLEL picks the parallel timings dom0 runs (`VERIFLAT_PARALLEL` of the dom0 build): `call` (the
# default), `mmap`, or `call,mmap`.
# Usage: [WORKTREE=<checkout>] [PARALLEL=call|mmap|call,mmap] build-parallel-call-image.sh [out_dir]
set -euo pipefail
BENCH=$(realpath "$(dirname "$0")")
WT=$(realpath "${WORKTREE:-$BENCH/../..}")
PARALLEL=${PARALLEL:-call}
mkdir -p "${1:-$BENCH/out/image}"; OUT_DIR=$(realpath "${1:-$BENCH/out/image}")
cd "$WT/boot"
VERIFLAT_PARALLEL=$PARALLEL cargo +1.99.1 build --profile release -p aloader -p kernel -p dom0 --features kernel/no-timer,dom0/no-timer
OUT=target/x86_64-unknown-none/release
cp "$OUT/aloader" "$OUT_DIR/aloader"
cat "$OUT/kernel" "$OUT/dom0" > "$OUT_DIR/jumbo"
if git -C "$WT" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    git -C "$WT" log -1 --format='%H %s' > "$OUT_DIR/built-from.txt"
    git -C "$WT" status --short -- src boot >> "$OUT_DIR/built-from.txt"
else
    echo "$WT (not a git checkout)" > "$OUT_DIR/built-from.txt"
    [ -f "$WT/SNAPSHOT_OF" ] && cat "$WT/SNAPSHOT_OF" >> "$OUT_DIR/built-from.txt"
fi
echo "parallel timings: $PARALLEL" >> "$OUT_DIR/built-from.txt"
sha256sum "$OUT_DIR/aloader" "$OUT_DIR/jumbo" >> "$OUT_DIR/built-from.txt"
