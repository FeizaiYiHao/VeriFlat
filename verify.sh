#!/usr/bin/env bash

set -u

CURRENT_DIR="$(cd "$(dirname "$0")" >/dev/null 2>&1 && pwd)"
VERUS_BIN="$CURRENT_DIR/verus/source/target-verus/release/verus"
COUNTER_DIR="$CURRENT_DIR/.verus-log"
COUNTER_FILE="$COUNTER_DIR/verify-count"
COUNTER_LOCK="$COUNTER_DIR/verify-count.lock"

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
flock -u 9

printf 'verification run #%s\n' "$run_count" >&2

# -Zthreads parallelizes rustc type checking and borrow checking.
verus_args=(-Zthreads=8 "$@")

# The final erasure check reruns rustc on the ghost-erased crate and does not
# depend on verification, so a --no-verify process runs it while the main
# process verifies with --no-erasure-check. Together they perform the same
# checks as one sequential run. Arguments that change the erasure check,
# write logs, or stop early keep the sequential run.
concurrent_erasure=1
for arg in "$@"; do
    case "$arg" in
        --compile|--no-verify|--no-erasure-check|--no-lifetime|--log*|-h|--help|--version|-V)
            concurrent_erasure=0 ;;
    esac
done
if (( ! concurrent_erasure )); then
    "$VERUS_BIN" "$CURRENT_DIR/src/lib.rs" "${verus_args[@]}"
    exit $?
fi

erasure_args=()
for arg in "${verus_args[@]}"; do
    case "$arg" in
        --output-json|--time|--time-expanded) ;;
        *) erasure_args+=("$arg") ;;
    esac
done
erasure_log="$(mktemp)"
erasure_pid=""
trap '[[ -n "$erasure_pid" ]] && kill "$erasure_pid" 2>/dev/null; rm -f "$erasure_log"' EXIT
"$VERUS_BIN" "$CURRENT_DIR/src/lib.rs" --no-verify "${erasure_args[@]}" > "$erasure_log" 2>&1 &
erasure_pid=$!

"$VERUS_BIN" "$CURRENT_DIR/src/lib.rs" --no-erasure-check "${verus_args[@]}"
status=$?
if (( status != 0 )); then
    # A sequential run skips the erasure check after a verification failure.
    exit "$status"
fi
wait "$erasure_pid"
erasure_status=$?
erasure_pid=""
if [[ -s "$erasure_log" ]]; then
    printf 'verify.sh: erasure check output:\n' >&2
    cat "$erasure_log" >&2
fi
exit "$erasure_status"
