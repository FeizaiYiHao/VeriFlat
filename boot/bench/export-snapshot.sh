#!/usr/bin/env bash
# Exports a commit of this checkout (default HEAD) into SNAP_DIR without git metadata, with `verus`
# linked to this checkout's Verus tree, so a boot image can be built from a fixed kernel while src/ is
# being edited: `WORKTREE=<snap_dir> build-parallel-call-image.sh`. OVERLAY lists working-copy files
# (paths relative to the checkout, such as boot/dom0/src/main.rs) copied over the export. SNAP_DIR/
# SNAPSHOT_OF records the commit and the overlaid files with their hashes; build-parallel-call-image.sh
# copies it into built-from.txt. SNAP_DIR must not exist yet.
# Usage: [OVERLAY="<path>..."] export-snapshot.sh <snap_dir> [commit]
set -euo pipefail
BENCH=$(realpath "$(dirname "$0")")
WT=$(realpath "$BENCH/../..")
SNAP=${1:?snap_dir}; COMMIT=${2:-HEAD}
[ ! -e "$SNAP" ] || { echo "$SNAP exists" >&2; exit 2; }
mkdir -p "$SNAP"; SNAP=$(realpath "$SNAP")
git -C "$WT" archive "$COMMIT" | tar -x -C "$SNAP"
rm -rf "$SNAP/verus"; ln -s "$(realpath "$WT/verus")" "$SNAP/verus"
git -C "$WT" log -1 --format='snapshot of %H %s' "$COMMIT" > "$SNAP/SNAPSHOT_OF"
for f in ${OVERLAY:-}; do
    cp "$WT/$f" "$SNAP/$f"
    echo "overlaid from the working copy: $(sha256sum "$SNAP/$f" | cut -c1-16) $f" >> "$SNAP/SNAPSHOT_OF"
done
cat "$SNAP/SNAPSHOT_OF"
