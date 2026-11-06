#!/usr/bin/env bash
# Boots VeriFlat under QEMU: aloader (multiboot) loads the kernel and dom0 from a jumbo initrd
# (kernel ELF followed by dom0 ELF). dom0 reports its result through isa-debug-exit, so QEMU
# exits with status (code << 1) | 1: 1 means dom0 passed.
#
# Usage: boot/run.sh [extra qemu args...]
# NO_TIMER=1 builds the kernel and dom0 with feature `no-timer`: no LAPIC timer, dom0 runs its timings only.
# VERIFLAT_BOOT_2M_BLOCKS=n (default 4) sets the free 2M blocks of the kernel build, the root container's 2M quota;
# VERIFLAT_BOOT_1G_BLOCKS=0|1 (default 1) sets the free 1G block [1 GiB, 2 GiB) of the kernel build, the root container's
# 1G quota (0 without CPUID pdpe1gb); `-m 2304` covers the 2 GiB page array.
# VERIFLAT_PARALLEL picks the parallel timings of a NO_TIMER dom0 (see bench/README.md).
set -euo pipefail
cd "$(dirname "$0")"

PROFILE=${PROFILE:-release}
cargo +1.99.1 build --profile "$PROFILE" -p aloader -p kernel -p dom0 ${NO_TIMER:+--features kernel/no-timer,dom0/no-timer}
OUT=target/x86_64-unknown-none/$PROFILE

JUMBO=$(mktemp --suffix=.veriflat-jumbo)
trap 'rm -f "$JUMBO"' EXIT
cat "$OUT/kernel" "$OUT/dom0" > "$JUMBO"

if [ -w /dev/kvm ]; then
    ACCEL=(-enable-kvm -cpu host -machine q35,kernel_irqchip=split)
else
    echo "warning: /dev/kvm not writable, falling back to TCG" >&2
    ACCEL=(-cpu max,+pcid -machine q35)
fi

qemu-system-x86_64 "${ACCEL[@]}" -smp ${SMP:-4} -m 2304 \
    -kernel "$OUT/aloader" -initrd "$JUMBO" \
    -nographic -serial mon:stdio \
    -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
    -device intel-iommu,aw-bits=48,intremap=on -device edu -nic none \
    -no-reboot "$@"
