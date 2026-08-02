#!/usr/bin/env bash
# Verify the crate and print cumulative SMT time/rlimit for every Verus module.
#
# Usage:
#   ./module_times.sh
#   ./module_times.sh -n 2
#   ./module_times.sh -n 2 kernel::implementation::locker_unlocker

set -euo pipefail

CURRENT_DIR="$(cd "$(dirname "$0")" >/dev/null 2>&1 && pwd)"
VERIFY="$CURRENT_DIR/verify.sh"
THREADS=32
MODULE=""

while [ $# -gt 0 ]; do
  case "$1" in
    -n) THREADS="$2"; shift 2 ;;
    *)
      if [ -z "$MODULE" ]; then
        MODULE="$1"; shift
      else
        printf 'usage: %s [-n threads] [module]\n' "$0" >&2; exit 2
      fi
      ;;
  esac
done

JSON="$CURRENT_DIR/.module_times.json"
ROWS="$CURRENT_DIR/.module_times.rows"
trap 'rm -f "$JSON" "$ROWS"' EXIT

ARGS=(--time --output-json --num-threads "$THREADS")
[ -n "$MODULE" ] && ARGS+=(--verify-only-module "$MODULE")
set +e
"$VERIFY" "${ARGS[@]}" 2>/dev/null > "$JSON"
verify_status=$?
set -e

awk '
  /"times-ms": *\{/ { in_times = 1 }
  in_times && actual_threads == 0 && /"num-threads":/ {
    v = $0; sub(/^[^0-9]*/, "", v); sub(/[^0-9].*$/, "", v)
    actual_threads = v + 0
  }
  in_times && actual_threads > 0 && wall_ms == 0 && /"total":/ {
    v = $0; sub(/^[^0-9]*/, "", v); sub(/[^0-9].*$/, "", v)
    wall_ms = v + 0
  }
  /"smt-run-module-times": *\[/ { in_modules = 1; next }
  in_modules && /"module":/ {
    module = $0; sub(/^[^:]*: *"/, "", module); sub(/".*$/, "", module)
    ms = 0; rl = 0
    next
  }
  in_modules && module != "" && /"time-micros":/ {
    v = $0; sub(/^[^0-9]*/, "", v); sub(/[^0-9].*$/, "", v)
    ms = v / 1000.0
    next
  }
  in_modules && module != "" && /"rlimit":/ {
    v = $0; sub(/^[^0-9]*/, "", v); sub(/[^0-9].*$/, "", v)
    rl = v + 0
    next
  }
  in_modules && module != "" && /"function-breakdown":/ {
    printf "%.1f\t%d\t%s\n", ms, rl, module
    total_ms += ms; total_rl += rl; count += 1
    module = ""
    next
  }
  END {
    printf "__TOTAL__\t%d\t%.1f\t%.0f\t%d\t%d\n", count, total_ms, total_rl, wall_ms, actual_threads
  }
' "$JSON" > "$ROWS"

total_line="$(awk -F '\t' '$1 == "__TOTAL__" { print }' "$ROWS")"
n_modules="$(printf '%s\n' "$total_line" | cut -f2)"
total_smt_ms="$(printf '%s\n' "$total_line" | cut -f3)"
total_rlimit="$(printf '%s\n' "$total_line" | cut -f4)"
wall_ms="$(printf '%s\n' "$total_line" | cut -f5)"
actual_threads="$(printf '%s\n' "$total_line" | cut -f6)"

printf '%9s  %12s  %s\n' 'SMT(ms)' 'rlimit' 'module'
printf -- '-%.0s' {1..100}; printf '\n'
awk -F '\t' '$1 != "__TOTAL__" { print }' "$ROWS" \
  | sort -t$'\t' -k1,1nr \
  | awk -F '\t' '{ printf "%9.1f  %12d  %s\n", $1, $2, $3 }'
printf -- '-%.0s' {1..100}; printf '\n'
printf '%9.1f  %12d  TOTAL over %d modules; wall %dms; verifier threads %d (requested %d)\n' \
  "$total_smt_ms" "$total_rlimit" "$n_modules" "$wall_ms" "$actual_threads" "$THREADS"

if [ "$verify_status" -ne 0 ]; then
  printf 'verification exited with status %d; timings may be incomplete\n' "$verify_status" >&2
  exit "$verify_status"
fi
