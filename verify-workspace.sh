#!/usr/bin/env bash

set -euo pipefail

CURRENT_DIR="$(cd "$(dirname "$0")" >/dev/null 2>&1 && pwd)"
CARGO_VERUS_BIN="$CURRENT_DIR/verus/source/target-verus/release/cargo-verus"
COUNTER_DIR="$CURRENT_DIR/.verus-log"
COUNTER_FILE="$COUNTER_DIR/verify-count"
COUNTER_LOCK="$COUNTER_DIR/verify-count.lock"
FOCUS_TARGET_DIR="$CURRENT_DIR/target/verus-partial"
FOCUS_STATE_DIR="$FOCUS_TARGET_DIR/.veriflat-focus-state"
FOCUS_STATE_LOCK="$FOCUS_TARGET_DIR/.veriflat-focus-state.lock"

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
  workspace: Cargo jobs=8, Verus threads=32
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
    cargo_jobs="${cargo_jobs:-8}"
    verus_threads="${verus_threads:-32}"
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

normalized_verus_args=()
if ((${#verus_args[@]} > 0)); then
    for verus_arg in "${verus_args[@]}"; do
        case "$verus_arg" in
            --time)
                # Timing is already enabled below. Accept repeated caller flags
                # without forwarding duplicates to Verus.
                ;;
            --num-threads|--num-threads=*)
                printf '%s is managed by --verus-threads\n' "$verus_arg" >&2
                exit 2
                ;;
            *)
                normalized_verus_args+=("$verus_arg")
                ;;
        esac
    done
fi
verus_args=()
if ((${#normalized_verus_args[@]} > 0)); then
    verus_args=("${normalized_verus_args[@]}")
fi

if [[ ! -x "$CARGO_VERUS_BIN" ]]; then
    printf 'verify-workspace.sh: Cargo-Verus binary is not executable: %s\n' \
        "$CARGO_VERUS_BIN" >&2
    exit 127
fi

export RUSTUP_TOOLCHAIN="${RUSTUP_TOOLCHAIN:-1.97.1-x86_64-unknown-linux-gnu}"
export PATH="$HOME/.cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

package_lines="$(
    VERIFLAT_REPO_DIR="$CURRENT_DIR" \
    VERIFLAT_FOCUS_PACKAGE="$package" \
    python3 - <<'PY'
import json
import os
import subprocess
import sys

repo = os.environ["VERIFLAT_REPO_DIR"]
focus = os.environ["VERIFLAT_FOCUS_PACKAGE"]
metadata = json.loads(subprocess.check_output(
    ["cargo", "metadata", "--format-version", "1", "--no-deps"],
    cwd=repo,
    text=True,
))
member_ids = set(metadata["workspace_members"])
packages = {
    package["name"]: package
    for package in metadata["packages"]
    if package["id"] in member_ids and package["name"] != "VeriFlat"
}

if not focus:
    selected = set(packages)
else:
    if focus not in packages:
        print(
            f"verify-workspace.sh: --package must name a split workspace package: {focus}",
            file=sys.stderr,
        )
        sys.exit(2)
    selected = set()
    pending = [focus]
    while pending:
        name = pending.pop()
        if name in selected:
            continue
        selected.add(name)
        pending.extend(
            dependency["name"]
            for dependency in packages[name]["dependencies"]
            if dependency["name"] in packages
        )

for name in sorted(selected):
    print(name)
PY
)"

run_packages=()
while IFS= read -r run_package; do
    [[ -z "$run_package" ]] || run_packages+=("$run_package")
done <<< "$package_lines"

if ((${#run_packages[@]} == 0)); then
    printf 'verify-workspace.sh: no split workspace packages selected\n' >&2
    exit 2
fi

focus_fingerprint="$(
    {
        printf '%s\0' "$run_kind" "$cargo_jobs" "$verus_threads"
        if ((${#verus_args[@]} > 0)); then
            printf '%s\0' "${verus_args[@]}"
        fi
    } | sha256sum | cut -d' ' -f1
)"

mkdir -p "$FOCUS_STATE_DIR"
exec 8>"$FOCUS_STATE_LOCK"
flock 8

stale_packages=()
declare -A desired_states=()
for run_package in "${run_packages[@]}"; do
    if [[ -z "$package" || "$run_package" == "$package" ]]; then
        desired_state="root:$focus_fingerprint"
    else
        desired_state="dependency"
    fi
    desired_states["$run_package"]="$desired_state"
    state_file="$FOCUS_STATE_DIR/$run_package"
    current_state=""
    if [[ -f "$state_file" ]]; then
        read -r current_state < "$state_file"
    fi
    if [[ "$current_state" != "$desired_state" ]]; then
        stale_packages+=("$run_package")
    fi
done

if ((${#stale_packages[@]} > 0)); then
    clean_args=()
    for stale_package in "${stale_packages[@]}"; do
        clean_args+=(-p "$stale_package")
    done
    printf 'invalidating partial artifacts for: %s\n' "${stale_packages[*]}" >&2
    cargo clean "${clean_args[@]}" --target-dir "$FOCUS_TARGET_DIR"
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
flock -u 9

printf 'verification run #%s (%s, Cargo jobs=%s, Verus threads=%s)\n' \
    "$run_count" "$run_kind" "$cargo_jobs" "$verus_threads" >&2

command=(
    "$CARGO_VERUS_BIN" focus "${cargo_args[@]}" -j "$cargo_jobs" --
    --num-threads "$verus_threads" --time
)
if ((${#verus_args[@]} > 0)); then
    command+=("${verus_args[@]}")
fi
"${command[@]}"

for run_package in "${run_packages[@]}"; do
    state_file="$FOCUS_STATE_DIR/$run_package"
    state_tmp="$state_file.$$"
    printf '%s\n' "${desired_states[$run_package]}" > "$state_tmp"
    mv "$state_tmp" "$state_file"
done
