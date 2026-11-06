#!/usr/bin/env bash
# KVM runs of the no-timer dom0 timings on stored boot images. The QEMU line is boot/run.sh's KVM line,
# then `-m $MEM -mem-prealloc` (MEM in MiB, default 6144; after run.sh's `-m 1024` and `-no-reboot`), pinned to
# host CPUs 0-31; mmap1g needs MEM=2304, since above about 2.75 GiB q35 ends low memory below 2 GiB with ACPI there;
# each run has a 300 s timeout. A run passes with QEMU exit status 1. For every run the timing lines go
# to <out>/extracted.txt and the status to <out>/status.txt; the raw log is deleted when the run passed
# and kept otherwise.
# Single mode boots IMAGE (default boot/bench/out/image) into OUT (default boot/bench/out/results).
# A/B mode, with B_IMAGE set, boots IMAGE then B_IMAGE (results into B_OUT, default
# boot/bench/out/results-b) for every run and SMP, so slow drift of the host hits both alike.
# Runs are numbered from FIRST_RUN (default 1), so later calls can add runs to the same directories.
# Usage: [MEM=<MiB>] [IMAGE=<dir>] [OUT=<dir>] [B_IMAGE=<dir> [B_OUT=<dir>]] [FIRST_RUN=<n>] run-parallel-call.sh <runs> <smp>...
set -uo pipefail
BENCH=$(realpath "$(dirname "$0")")
RUNS=${1:?runs}; shift
[ $# -gt 0 ] || { echo "usage: run-parallel-call.sh <runs> <smp>..." >&2; exit 2; }
FIRST=${FIRST_RUN:-1}
MEM=${MEM:-6144}
SETS=("$(realpath "${IMAGE:-$BENCH/out/image}")" "${OUT:-$BENCH/out/results}")
if [ -n "${B_IMAGE:-}" ]; then
    SETS+=("$(realpath "$B_IMAGE")" "${B_OUT:-$BENCH/out/results-b}")
fi
for ((i = 1; i < ${#SETS[@]}; i += 2)); do
    mkdir -p "${SETS[i]}"; SETS[i]=$(realpath "${SETS[i]}")
done
for run in $(seq "$FIRST" $((FIRST + RUNS - 1))); do
    for smp in "$@"; do
        for ((i = 0; i < ${#SETS[@]}; i += 2)); do
            img=${SETS[i]}; out=${SETS[i + 1]}; log="$out/smp$smp-run$run.log"
            timeout 300 taskset -c 0-31 /usr/bin/qemu-system-x86_64 -enable-kvm -cpu host -machine q35,kernel_irqchip=split \
                -smp "$smp" -m 1024 -kernel "$img/aloader" -initrd "$img/jumbo" -nographic -serial mon:stdio \
                -device isa-debug-exit,iobase=0xf4,iosize=0x04 -device intel-iommu,aw-bits=48,intremap=on -device edu -nic none \
                -no-reboot -m "$MEM" -mem-prealloc </dev/null >"$log" 2>&1
            status=$?
            echo "smp=$smp run=$run status=$status" | tee -a "$out/status.txt"
            grep -a -E "parallel_call|unmapn|round trip|null syscall|mmap|new_thread:|CPUs present|timings passed|panic|ERROR|error|timed out" "$log" \
                | sed "s/^/smp=$smp run=$run: /" >> "$out/extracted.txt"
            [ "$status" = 1 ] && rm -f "$log"
        done
    done
done
