#!/usr/bin/env bash
# Boots VeriFlat under QEMU: aloader (multiboot) loads the kernel and dom0 from a jumbo initrd
# (kernel ELF followed by dom0 ELF). dom0 reports its result through isa-debug-exit, so QEMU
# exits with status (code << 1) | 1: 1 means dom0 passed.
#
# Usage: boot/run.sh [extra qemu args...]
# NO_TIMER=1 builds the kernel with feature `no-timer` (no LAPIC timer); dom0's self-test needs no tick.
# VERIFLAT_BOOT_2M_BLOCKS=n (default 4) sets the free 2M blocks of the kernel build, the root container's 2M quota;
# VERIFLAT_BOOT_1G_BLOCKS=0|1 (default 1) sets the free 1G block [1 GiB, 2 GiB) of the kernel build, the root container's
# 1G quota (0 without CPUID pdpe1gb). The page array covers [0, 4 GiB); `-m 2304` is RAM, the rest stays Unavailable,
# BAR pages included: device memory is described by the PCI table's BAR slots, not by the page array.
# Devices: `intel-iommu` (VT-d, required), `edu` (IOMMU self-test), and an NVMe controller behind the PCIe root port
# rp1 (`-device pcie-root-port,id=rp1,chassis=1 -drive file=$OUT/nvme.img,if=none,id=nvm,format=raw
# -device nvme,drive=nvm,serial=veriflat0,bus=rp1`), as an SSD sits on a real server, so every boot takes the loader
# across a PCI-to-PCI bridge; it is backed by a 64 MiB sparse raw image created once in the build output directory.
# The loader maps every page of every assigned memory BAR into dom0 at 0xd0_0000_0000 + physical address as a 4K IO
# leaf, BARs above 4 GiB too. A high BAR for a test: append
# `-object memory-backend-ram,id=hm,size=2G -device ivshmem-plain,memdev=hm` (SeaBIOS places the 2 GiB BAR2 above
# 4 GiB); dom0's `io_high_bar` check then writes and reads it.
# `+invtsc` makes the TSC rate known to QEMU, which then reports it in the hypervisor leaf 4000_0010H.
# NVME_BLOCK_SIZE=4096 (default 512) formats the emulated NVMe namespace with that logical block size.
set -euo pipefail
cd "$(dirname "$0")"

PROFILE=${PROFILE:-release}
BUILD_FEATURES=()
if [ -n "${NO_TIMER:-}" ]; then BUILD_FEATURES+=(--features kernel/no-timer); fi
cargo +1.99.1 build --profile "$PROFILE" -p aloader -p kernel -p dom0 "${BUILD_FEATURES[@]}"
OUT=target/x86_64-unknown-none/$PROFILE

[ -f "$OUT/nvme.img" ] || qemu-img create -q -f raw "$OUT/nvme.img" 64M

JUMBO=$(mktemp --suffix=.veriflat-jumbo)
trap 'rm -f "$JUMBO"' EXIT
cat "$OUT/kernel" "$OUT/dom0" > "$JUMBO"

if [ -w /dev/kvm ]; then
    ACCEL=(-enable-kvm -cpu host,+invtsc -machine q35,kernel_irqchip=split)
else
    echo "warning: /dev/kvm not writable, falling back to TCG" >&2
    ACCEL=(-cpu max,+pcid -machine q35)
fi

qemu-system-x86_64 "${ACCEL[@]}" -smp ${SMP:-4} -m 2304 \
    -kernel "$OUT/aloader" -initrd "$JUMBO" \
    -nographic -serial mon:stdio \
    -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
    -device intel-iommu,aw-bits=48,intremap=on -device edu,dma_mask=0xffffffffffff -nic none \
    -device pcie-root-port,id=rp1,chassis=1 \
    -drive file="$OUT/nvme.img",if=none,id=nvm,format=raw -device nvme,drive=nvm,serial=veriflat0,bus=rp1,logical_block_size=${NVME_BLOCK_SIZE:-512},physical_block_size=${NVME_BLOCK_SIZE:-512} \
    -no-reboot "$@"
