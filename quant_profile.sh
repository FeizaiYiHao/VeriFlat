#!/usr/bin/env bash
# Run one Verus verification with Z3's quantifier profiler enabled, then rank
# quantifiers by breadth and depth. Repeated reports for the same quantifier
# are combined: instantiations are summed and max-generation takes the maximum.

set -euo pipefail

CURRENT_DIR="$(cd "$(dirname "$0")" >/dev/null 2>&1 && pwd)"
VERIFY="$CURRENT_DIR/verify.sh"
TOP=20
SORT_BY="score"
INPUT=""
VERUS_ARGS=()

usage() {
    cat <<'EOF'
Usage:
  ./quant_profile.sh [--top N] [--sort score|width|depth] [--] VERUS_ARGS...
  ./quant_profile.sh [--top N] [--sort score|width|depth] --input PROFILE_OUTPUT

The default score is:

  instantiations * (max-generation + 1)

Examples:
  ./quant_profile.sh -- --verify-only-module pagetable_seq::pagetable_spec
  ./quant_profile.sh --top 50 --sort depth -- --verify-root
  ./quant_profile.sh --input saved-profile.log
EOF
}

while (($# > 0)); do
    case "$1" in
        --top|-n)
            (($# >= 2)) || { printf '%s requires a value\n' "$1" >&2; exit 2; }
            TOP="$2"
            shift 2
            ;;
        --sort)
            (($# >= 2)) || { printf '%s requires a value\n' "$1" >&2; exit 2; }
            SORT_BY="$2"
            shift 2
            ;;
        --input)
            (($# >= 2)) || { printf '%s requires a value\n' "$1" >&2; exit 2; }
            INPUT="$2"
            shift 2
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        --)
            shift
            VERUS_ARGS+=("$@")
            break
            ;;
        *)
            VERUS_ARGS+=("$1")
            shift
            ;;
    esac
done

[[ "$TOP" =~ ^[1-9][0-9]*$ ]] || {
    printf 'invalid --top value: %s\n' "$TOP" >&2
    exit 2
}
case "$SORT_BY" in
    score) SORT_COLUMN=1 ;;
    width) SORT_COLUMN=2 ;;
    depth) SORT_COLUMN=3 ;;
    *)
        printf 'invalid --sort value: %s (expected score, width, or depth)\n' "$SORT_BY" >&2
        exit 2
        ;;
esac
if [[ -n "$INPUT" && ${#VERUS_ARGS[@]} -ne 0 ]]; then
    printf -- '--input cannot be combined with Verus arguments\n' >&2
    exit 2
fi

mkdir -p "$CURRENT_DIR/.verus-log"
ROWS="$(mktemp "$CURRENT_DIR/.verus-log/quant-profile.rows.XXXXXX")"
RAW=""
trap 'rm -f "$ROWS" ${RAW:+"$RAW"}' EXIT

verify_status=0
if [[ -n "$INPUT" ]]; then
    [[ -r "$INPUT" ]] || { printf 'cannot read profile output: %s\n' "$INPUT" >&2; exit 2; }
    PROFILE_OUTPUT="$INPUT"
else
    RAW="$(mktemp "$CURRENT_DIR/.verus-log/quant-profile.raw.XXXXXX")"
    set +e
    "$VERIFY" --smt-option smt.qi.profile=true "${VERUS_ARGS[@]}" 2>&1 \
        | tee "$RAW" \
        | sed '/^\[quantifier_instances\]/d'
    verify_status=${PIPESTATUS[0]}
    set -e
    PROFILE_OUTPUT="$RAW"
fi

awk '
    /^\[quantifier_instances\]/ {
        line = $0
        sub(/^\[quantifier_instances\][[:space:]]*/, "", line)
        n = split(line, field, /[[:space:]]*:[[:space:]]*/)
        if (n < 6) next

        name = field[1]
        instances = field[2] + 0
        generation = field[5] + 0
        width[name] += instances
        reports[name] += 1
        if (!(name in depth) || generation > depth[name]) depth[name] = generation
    }
    END {
        for (name in width) {
            score = width[name] * (depth[name] + 1)
            printf "%.0f\t%.0f\t%.0f\t%d\t%s\n", score, width[name], depth[name], reports[name], name
        }
    }
' "$PROFILE_OUTPUT" > "$ROWS"

if [[ ! -s "$ROWS" ]]; then
    printf 'quant_profile.sh: no [quantifier_instances] records found\n' >&2
    printf 'Make sure this is a Z3 run and smt.qi.profile is not overridden.\n' >&2
    ((verify_status != 0)) && exit "$verify_status"
    exit 1
fi

printf '\nTop %d quantifiers by %s\n' "$TOP" "$SORT_BY"
printf '%14s  %14s  %14s  %7s  %s\n' 'score' 'instances' 'max-generation' 'reports' 'quantifier'
printf -- '-%.0s' {1..110}; printf '\n'
sort -t$'\t' -k"$SORT_COLUMN","$SORT_COLUMN"nr -k1,1nr -k2,2nr -k3,3nr "$ROWS" \
    | awk -F '\t' -v top="$TOP" '
        NR <= top {
            printf "%14d  %14d  %14d  %7d  %s\n", $1, $2, $3, $4, $5
        }
    '

if ((verify_status != 0)); then
    printf 'verification exited with status %d; ranking may be incomplete\n' "$verify_status" >&2
fi
exit "$verify_status"
