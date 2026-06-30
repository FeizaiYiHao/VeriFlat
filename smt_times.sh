#!/usr/bin/env bash
# smt_times.sh — verify the whole crate (or one module) and list every
# function whose SMT solver time exceeds THRESHOLD_MS (default 100), sorted
# slowest-first.
#
# Usage:
#   ./smt_times.sh                         # whole crate
#   ./smt_times.sh <module::path>          # one module
#   ./smt_times.sh -n 8                    # whole crate, 8 verifier threads
#   ./smt_times.sh -n 8 kernel::implementation::syscall_alloc_quota
#
# Columns: SMT(ms)  rlimit  ok  mode  function
# (rlimit is the solver-effort metric — more stable across machines than ms.)
# Only functions with SMT(ms) > THRESHOLD_MS are printed; the TOTAL line still
# sums ALL functions and notes how many fell below the cutoff.
#
# Pure bash/awk/sort: no python or jq (both are blocked in this sandbox).
# Relies on Verus' --output-json layout being pretty-printed with one field
# per line and a fixed per-entry order (function, mode:, time, time-micros,
# rlimit, success). Module-level time-micros/rlimit precede the first
# "function": line, so the awk pass (which only starts a record at "function":)
# never mistakes them for per-function values.

set -euo pipefail
CURRENT_DIR="$( cd "$( dirname "$0" )" >/dev/null 2>&1 && pwd )"
VERUS="$CURRENT_DIR/verus/source/target-verus/release/verus"

# Only print functions whose SMT time exceeds this many milliseconds.
THRESHOLD_MS=100

THREADS=4
MODULE=""
while [ $# -gt 0 ]; do
  case "$1" in
    -n) THREADS="$2"; shift 2 ;;
    *)  MODULE="$1"; shift ;;
  esac
done

ARGS=("$CURRENT_DIR/src/lib.rs" --time --output-json --num-threads "$THREADS")
[ -n "$MODULE" ] && ARGS+=(--verify-only-module "$MODULE")

# Temp JSON stays inside the project tree (/tmp is outside the sandbox).
JSON="$CURRENT_DIR/.smt_times.json"
trap 'rm -f "$JSON"' EXIT

# JSON → stdout; build noise + `note:` lines → stderr (discarded).
"$VERUS" "${ARGS[@]}" 2>/dev/null > "$JSON" || true

awk '
  /"function":/ {
    # Start a new record. Extract the value between the quotes after the colon.
    name = $0; sub(/^[^:]*: *"/, "", name); sub(/".*$/, "", name)
    in_rec = 1; mode = ""; ms = 0; rl = 0
    next
  }
  in_rec && /"mode:?":/ {
    mode = $0; sub(/^[^:]*:[^:]*: *"/, "", mode); sub(/".*$/, "", mode); next
  }
  in_rec && /"time-micros":/ {
    v = $0; sub(/^[^0-9]*/, "", v); sub(/[^0-9].*$/, "", v); ms = v / 1000.0; next
  }
  in_rec && /"rlimit":/ {
    v = $0; sub(/^[^0-9]*/, "", v); sub(/[^0-9].*$/, "", v); rl = v; next
  }
  in_rec && /"success":/ {
    ok = ($0 ~ /true/) ? "Y" : "N"
    printf "%.1f\t%d\t%s\t%s\t%s\n", ms, rl, ok, mode, name
    total += ms; n += 1
    in_rec = 0; next
  }
  END {
    printf "__TOTAL__\t%d\t%.1f\n", n, total
  }
' "$JSON" > "$JSON.rows"

# Split the TOTAL sentinel off, sort the rest slowest-first, then print.
total_line="$(grep '^__TOTAL__' "$JSON.rows" || true)"
n_funcs="$(printf '%s' "$total_line" | cut -f2)"
total_ms="$(printf '%s' "$total_line" | cut -f3)"

# Keep only rows above the threshold, sorted slowest-first.
shown="$(grep -v '^__TOTAL__' "$JSON.rows" \
  | awk -F'\t' -v th="$THRESHOLD_MS" '$1 > th' \
  | sort -t$'\t' -k1,1 -nr)"
n_shown="$(printf '%s' "$shown" | grep -c . || true)"
n_hidden=$(( n_funcs - n_shown ))

printf '%9s  %10s  %2s  %-5s  %s\n' "SMT(ms)" "rlimit" "ok" "mode" "function"
printf -- '-%.0s' {1..90}; printf '\n'
printf '%s\n' "$shown" \
  | awk -F'\t' 'NF >= 5 { printf "%9.1f  %10d  %2s  %-5s  %s\n", $1, $2, $3, $4, $5 }'
printf -- '-%.0s' {1..90}; printf '\n'
printf '%9s  %10s      %-5s  TOTAL over %s functions (%s shown > %sms, %s below cutoff)\n' \
  "$total_ms" "" "" "$n_funcs" "$n_shown" "$THRESHOLD_MS" "$n_hidden"

rm -f "$JSON.rows"
