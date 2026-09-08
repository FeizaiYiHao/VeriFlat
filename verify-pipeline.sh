#!/usr/bin/env bash
# Cargo-Verus pipeline; optional cold VeriFlat artifacts, retaining dependency caches.
set -euo pipefail
CURRENT_DIR="$(cd "$(dirname "$0")" && pwd)"
cold=false
args=()
while (($#)); do
    case "$1" in
        --cold-veriflat) cold=true; shift ;;
        --) shift; args=("$@"); break ;;
        -h|--help)
            printf 'Usage: %s [--cold-veriflat] [-- VERUS_ARGS...]\nCargo default concurrency; Verus defaults to 32 threads.\n' "$0"
            exit 0 ;;
        *) printf 'unknown argument: %s\n' "$1" >&2; exit 2 ;;
    esac
done
export RUSTUP_TOOLCHAIN="${RUSTUP_TOOLCHAIN:-1.97.1-x86_64-unknown-linux-gnu}"
export PATH="$HOME/.cargo/bin:$PATH"
cd "$CURRENT_DIR"
if "$cold"; then
    packages=()
    for manifest in crates/*/Cargo.toml; do packages+=(-p "$(basename "$(dirname "$manifest")")"); done
    cargo clean "${packages[@]}"
fi
mkdir -p .verus-log
exec 9>.verus-log/verify-count.lock
flock 9
run_count=0
[[ ! -f .verus-log/verify-count ]] || read -r run_count < .verus-log/verify-count
[[ "$run_count" =~ ^[0-9]+$ ]] || { printf 'invalid verification counter\n' >&2; exit 2; }
run_count=$((run_count + 1))
printf '%s\n' "$run_count" > ".verus-log/verify-count.$$"
mv ".verus-log/verify-count.$$" .verus-log/verify-count
{
    printf '%s\t%s\tpipeline\tcargo_jobs=default\tverus_threads_default=32\tcold_veriflat=%s' "$run_count" "$(date -u +'%Y-%m-%dT%H:%M:%SZ')" "$cold"
    printf '\t%q' "${args[@]}"
    printf '\n'
} >> .verus-log/verify-runs.log
flock -u 9
printf 'verification run #%s (pipeline; Cargo default; cold VeriFlat=%s; dependency caches retained)\n' "$run_count" "$cold" >&2
exec env VERUS_PIPELINE_SMT=1 "$CURRENT_DIR/verus/source/target-verus/release/cargo-verus" \
    verify --workspace --exclude VeriFlat -- --num-threads 32 --time "${args[@]}"
