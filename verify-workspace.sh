#!/usr/bin/env bash

set -euo pipefail

CURRENT_DIR="$(cd "$(dirname "$0")" >/dev/null 2>&1 && pwd)"
CARGO_VERUS_BIN="$CURRENT_DIR/verus/source/target-verus/release/cargo-verus"
COUNTER_DIR="$CURRENT_DIR/.verus-log"
COUNTER_FILE="$COUNTER_DIR/verify-count"
COUNTER_LOCK="$COUNTER_DIR/verify-count.lock"
RUN_LOG="$COUNTER_DIR/verify-runs.log"

package=""
cargo_jobs=""
verus_threads=""
verus_args=()

usage() {
    cat <<'EOF'
Usage:
  ./verify-workspace.sh
  ./verify-workspace.sh --package PACKAGE
  ./verify-workspace.sh [--cargo-jobs N] [--verus-threads N] [-- VERUS_ARGS...]

Defaults:
  workspace: Cargo jobs=2, Verus threads=16
  focused:   Cargo jobs=1, Verus threads=32
EOF
}

while (($# > 0)); do
    case "$1" in
        -p|--package)
            (($# >= 2)) || { printf 'missing package after %s\n' "$1" >&2; exit 2; }
            package="$2"
            shift 2
            ;;
        --cargo-jobs)
            (($# >= 2)) || { printf 'missing value after %s\n' "$1" >&2; exit 2; }
            cargo_jobs="$2"
            shift 2
            ;;
        --verus-threads)
            (($# >= 2)) || { printf 'missing value after %s\n' "$1" >&2; exit 2; }
            verus_threads="$2"
            shift 2
            ;;
        --)
            shift
            verus_args=("$@")
            break
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            printf 'unknown argument: %s\n' "$1" >&2
            usage >&2
            exit 2
            ;;
    esac
done

if [[ -n "$package" ]]; then
    cargo_jobs="${cargo_jobs:-1}"
    verus_threads="${verus_threads:-32}"
    cargo_args=(-p "$package")
    run_kind="focus:$package"
else
    cargo_jobs="${cargo_jobs:-2}"
    verus_threads="${verus_threads:-16}"
    cargo_args=(--workspace --exclude VeriFlat)
    run_kind="workspace"
fi

for value_name in cargo_jobs verus_threads; do
    value="${!value_name}"
    if [[ ! "$value" =~ ^[1-9][0-9]*$ ]]; then
        printf '%s must be a positive integer: %q\n' "$value_name" "$value" >&2
        exit 2
    fi
done

if [[ ! -x "$CARGO_VERUS_BIN" ]]; then
    printf 'verify-workspace.sh: Cargo-Verus binary is not executable: %s\n' \
        "$CARGO_VERUS_BIN" >&2
    exit 127
fi

mkdir -p "$COUNTER_DIR"
exec 9>"$COUNTER_LOCK"
flock 9
run_count=0
if [[ -f "$COUNTER_FILE" ]]; then
    read -r run_count < "$COUNTER_FILE"
fi
if [[ ! "$run_count" =~ ^[0-9]+$ ]]; then
    printf 'verify-workspace.sh: invalid counter in %s: %q\n' \
        "$COUNTER_FILE" "$run_count" >&2
    exit 2
fi
run_count=$((run_count + 1))
counter_tmp="$COUNTER_FILE.$$"
printf '%s\n' "$run_count" > "$counter_tmp"
mv "$counter_tmp" "$COUNTER_FILE"
{
    printf '%s\t%s\tworkspace:%s\tcargo_jobs=%s\tverus_threads=%s' \
        "$run_count" "$(date -u +'%Y-%m-%dT%H:%M:%SZ')" "$run_kind" \
        "$cargo_jobs" "$verus_threads"
    printf '\t%q' "${verus_args[@]}"
    printf '\n'
} >> "$RUN_LOG"
flock -u 9

printf 'verification run #%s (%s, Cargo jobs=%s, Verus threads=%s)\n' \
    "$run_count" "$run_kind" "$cargo_jobs" "$verus_threads" >&2

export RUSTUP_TOOLCHAIN="${RUSTUP_TOOLCHAIN:-1.97.1-x86_64-unknown-linux-gnu}"
export PATH="$HOME/.cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

exec "$CARGO_VERUS_BIN" focus "${cargo_args[@]}" -j "$cargo_jobs" -- \
    --num-threads "$verus_threads" --time "${verus_args[@]}"
