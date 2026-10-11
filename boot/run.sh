#!/usr/bin/env bash
# Boots VeriFlat under QEMU: aloader (multiboot) loads the kernel and dom0 from a jumbo initrd
# (kernel ELF followed by dom0 ELF). dom0 reports its result through isa-debug-exit, so QEMU
# exits with status (code << 1) | 1: 1 means dom0 passed.
#
# Usage: boot/run.sh [extra qemu args...]
set -euo pipefail
cd "$(dirname "$0")"

PROFILE=${PROFILE:-release}
cargo +1.97.1 build --profile "$PROFILE" -p aloader -p kernel -p dom0
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

qemu-system-x86_64 "${ACCEL[@]}" -smp ${SMP:-4} -m 1024 \
    -kernel "$OUT/aloader" -initrd "$JUMBO" \
    -nographic -serial mon:stdio \
    -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
    -device intel-iommu,aw-bits=48 -device edu -nic none \
    -no-reboot "$@"
