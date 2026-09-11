#!/usr/bin/env bash
# Shared temporary capture for smt_times.sh and module_times.sh.
set -euo pipefail
CURRENT_DIR="$(cd "$(dirname "$0")" && pwd)"
mode="$1"
shift
threads=32
module=""
while (($#)); do
    case "$1" in
        -n)
            (($# >= 2)) || { printf 'missing thread count\n' >&2; exit 2; }
            threads="$2"; shift 2 ;;
        *)
            [[ -z "$module" && "$1" != -* ]] || { printf 'expected [-n threads] [module]\n' >&2; exit 2; }
            module="$1"; shift ;;
    esac
done
[[ "$threads" =~ ^[1-9][0-9]*$ ]] || { printf 'threads must be positive\n' >&2; exit 2; }
args=(--time --output-json --num-threads "$threads")
[[ -z "$module" ]] || args+=(--verify-only-module "$module")
timing_dir="$(mktemp -d "${TMPDIR:-/tmp}/veriflat-timings.XXXXXXXX")"
trap 'rm -rf -- "$timing_dir"' EXIT
verify_status=0
/usr/bin/time -f '%e' -o "$timing_dir/wall.seconds" "$CURRENT_DIR/verify.sh" "${args[@]}" \
    > "$timing_dir/verus.json" 2> "$timing_dir/stderr.log" || verify_status=$?
cat "$timing_dir/stderr.log" >&2
report_args=(--threshold-ms 100)
[[ "$mode" != modules ]] || report_args=(--modules)
report_status=0
python3 "$CURRENT_DIR/smt_parse.py" "$timing_dir/verus.json" "${report_args[@]}" || report_status=$?
printf 'External wall (seconds): %s\n' "$(tail -n 1 "$timing_dir/wall.seconds")" >&2
printf 'Scope: monolith %s; prebuilt vstd; Verus threads=%s; exit=%s\n' "${module:-all modules}" "$threads" "$verify_status" >&2
((verify_status == 0)) || exit "$verify_status"
exit "$report_status"
