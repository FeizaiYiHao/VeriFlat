#!/usr/bin/env bash
# Boots VeriFlat under QEMU: aloader (multiboot) loads the kernel and dom0 from a jumbo initrd
# (kernel ELF followed by dom0 ELF). dom0 reports its result through isa-debug-exit, so QEMU
# exits with status (code << 1) | 1: 1 means dom0 passed.
#
# Usage: boot/run.sh [extra qemu args...]
# NO_TIMER=1 builds the kernel and dom0 with feature `no-timer`: no LAPIC timer, dom0 runs its timings only.
# DMA_WRITE_TEST=1 runs only the opt-in EDU device-to-RAM revocation regression.
# VERIFLAT_BOOT_2M_BLOCKS=n (default 4) sets the free 2M blocks of the kernel build, the root container's 2M quota;
# VERIFLAT_BOOT_1G_BLOCKS=0|1 (default 1) sets the free 1G block [1 GiB, 2 GiB) of the kernel build, the root container's
# 1G quota (0 without CPUID pdpe1gb). The page array covers [0, 4 GiB); `-m 2304` is RAM, the rest stays Unavailable
# except the BAR0 pages of the recorded PCI functions.
# Devices: `intel-iommu` (VT-d, required), `edu` (DMA self-test), and an NVMe controller
# (`-drive file=$OUT/nvme.img,if=none,id=nvm,format=raw -device nvme,drive=nvm,serial=veriflat0`) backed by a
# 64 MiB sparse raw image created once in the build output directory; the loader maps the BAR0 of the NVMe and edu
# functions into dom0 at 0xd0_0000_0000 + physical address.
# VERIFLAT_PARALLEL picks the parallel timings of a NO_TIMER dom0 (see bench/README.md).
set -euo pipefail
cd "$(dirname "$0")"

PROFILE=${PROFILE:-release}
BUILD_FEATURES=()
if [ -n "${NO_TIMER:-}" ]; then BUILD_FEATURES+=(--features kernel/no-timer,dom0/no-timer); fi
if [ "${DMA_WRITE_TEST:-0}" = 1 ]; then BUILD_FEATURES+=(--features dom0/dma-write-test); fi
cargo +1.99.1 build --profile "$PROFILE" -p aloader -p kernel -p dom0 "${BUILD_FEATURES[@]}"
OUT=target/x86_64-unknown-none/$PROFILE

[ -f "$OUT/nvme.img" ] || qemu-img create -q -f raw "$OUT/nvme.img" 64M

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
    -device intel-iommu,aw-bits=48,intremap=on -device edu,dma_mask=0xffffffffffff -nic none \
    -drive file="$OUT/nvme.img",if=none,id=nvm,format=raw -device nvme,drive=nvm,serial=veriflat0 \
    -no-reboot "$@"
