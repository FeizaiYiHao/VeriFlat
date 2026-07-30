#!/usr/bin/env bash

set -u

CURRENT_DIR="$(cd "$(dirname "$0")" >/dev/null 2>&1 && pwd)"
VERUS_BIN="$CURRENT_DIR/verus/source/target-verus/release/verus"
COUNTER_DIR="$CURRENT_DIR/.verus-log"
COUNTER_FILE="$COUNTER_DIR/verify-count"
COUNTER_LOCK="$COUNTER_DIR/verify-count.lock"
RUN_LOG="$COUNTER_DIR/verify-runs.log"

if [[ ! -x "$VERUS_BIN" ]]; then
    printf 'verify.sh: Verus binary is not executable: %s\n' "$VERUS_BIN" >&2
    exit 127
fi

mkdir -p "$COUNTER_DIR"

# Serialize the read-modify-write so parallel module checks receive distinct
# run numbers. The state lives under .verus-log/, which is already gitignored.
exec 9>"$COUNTER_LOCK"
flock 9
run_count=0
if [[ -f "$COUNTER_FILE" ]]; then
    read -r run_count < "$COUNTER_FILE"
fi
if [[ ! "$run_count" =~ ^[0-9]+$ ]]; then
    printf 'verify.sh: invalid counter in %s: %q\n' "$COUNTER_FILE" "$run_count" >&2
    exit 2
fi
run_count=$((run_count + 1))
counter_tmp="$COUNTER_FILE.$$"
printf '%s\n' "$run_count" > "$counter_tmp"
mv "$counter_tmp" "$COUNTER_FILE"
{
    printf '%s\t%s' "$run_count" "$(date -u +'%Y-%m-%dT%H:%M:%SZ')"
    printf '\t%q' "$@"
    printf '\n'
} >> "$RUN_LOG"
flock -u 9

printf 'verification run #%s\n' "$run_count" >&2
"$VERUS_BIN" "$CURRENT_DIR/src/lib.rs" "$@"
