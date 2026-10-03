#!/usr/bin/env bash
# Verify the noninterference workspace: the user-projection facts crate and the
# noninterference crate. Kernel dependencies are compiled for their
# exported specifications but not reverified; verify them with the kernel's
# own scripts.

set -euo pipefail

CURRENT_DIR="$(cd "$(dirname "$0")" >/dev/null 2>&1 && pwd)"
REPO_DIR="$(dirname "$CURRENT_DIR")"
CARGO_VERUS_BIN="$REPO_DIR/verus/source/target-verus/release/cargo-verus"
COUNTER_DIR="$REPO_DIR/.verus-log"
COUNTER_FILE="$COUNTER_DIR/verify-count"
COUNTER_LOCK="$COUNTER_DIR/verify-count.lock"

if [[ ! -x "$CARGO_VERUS_BIN" ]]; then
    printf 'verify-ni.sh: Cargo-Verus binary is not executable: %s\n' "$CARGO_VERUS_BIN" >&2
    exit 127
fi

export RUSTUP_TOOLCHAIN="${RUSTUP_TOOLCHAIN:-1.97.1-x86_64-unknown-linux-gnu}"
export PATH="$HOME/.cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

mkdir -p "$COUNTER_DIR"
exec 9>"$COUNTER_LOCK"
flock 9
run_count=0
if [[ -f "$COUNTER_FILE" ]]; then
    read -r run_count < "$COUNTER_FILE"
fi
if [[ ! "$run_count" =~ ^[0-9]+$ ]]; then
    printf 'verify-ni.sh: invalid counter in %s: %q\n' "$COUNTER_FILE" "$run_count" >&2
    exit 2
fi
run_count=$((run_count + 1))
counter_tmp="$COUNTER_FILE.$$"
printf '%s\n' "$run_count" > "$counter_tmp"
mv "$counter_tmp" "$COUNTER_FILE"
flock -u 9

printf 'verification run #%s (noninterference)\n' "$run_count" >&2

cd "$CURRENT_DIR"
"$CARGO_VERUS_BIN" focus --workspace -j 8 -- --num-threads 32 --time "$@"
