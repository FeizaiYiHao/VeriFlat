#!/usr/bin/env bash
# Boots VeriFlat with the benchmark dom0 (boot/dom0-bench) under QEMU: aloader (multiboot) loads the kernel and
# dom0-bench from a jumbo initrd (kernel ELF followed by dom0-bench ELF). dom0 reports its result through
# isa-debug-exit, so QEMU exits with status (code << 1) | 1: 1 means dom0 passed. boot/run.sh boots main's small
# self-test dom0 (boot/dom0) the same way.
#
# Usage: boot/bench/run.sh [extra qemu args...]
# NO_TIMER=1 builds the kernel and dom0 with feature `no-timer`: no LAPIC timer, dom0 runs its timings only.
# DMA_WRITE_TEST=1 runs only the opt-in EDU device-to-RAM revocation regression.
# ICE_BENCH=1 runs only the E810 (ice) packet benchmark, which QEMU has no device for: dom0 logs that it is skipped.
# ICE_XPROC=1 runs only its linked-in vs cross-process (IPC per batch) variant, skipped likewise; ICE_MOCK=1 runs that
# variant on the driver's software device model instead (numbers of the IPC and the model, not of a NIC).
# ICE_CHAN_MOCK=1 runs only the two-process ice::chan shapes (src/ice_chan.rs) on that model; VERIFLAT_ICE_SHAPE,
# VERIFLAT_ICE_PATH (zero, copy, map), VERIFLAT_ICE_TOUCH, VERIFLAT_ICE_FRAME, VERIFLAT_ICE_MODE, .. pick what it runs.
# PAYLOAD_PATH=1 adds feature dom0-bench/payload-path, which path copy or map, a payload touch, frames above 1518 bytes
# and VERIFLAT_PARALLEL=iommu,handoff / flushcpus need (without it such a build fails).
# VERIFLAT_BOOT_2M_BLOCKS=n (default 4) sets the free 2M blocks of the kernel build, the root container's 2M quota;
# VERIFLAT_BOOT_1G_BLOCKS=0|1 (default 1) sets the free 1G block [1 GiB, 2 GiB) of the kernel build, the root container's
# 1G quota (0 without CPUID pdpe1gb). The page array covers [0, 4 GiB); `-m 2304` is RAM, the rest stays Unavailable,
# BAR pages included: device memory is described by the PCI table's BAR slots, not by the page array.
# Devices: `intel-iommu` (VT-d, required), `edu` (DMA self-test), and an NVMe controller behind the PCIe root port
# rp1 (`-device pcie-root-port,id=rp1,chassis=1 -drive file=$OUT/nvme.img,if=none,id=nvm,format=raw
# -device nvme,drive=nvm,serial=veriflat0,bus=rp1`), as an SSD sits on a real server, so every boot takes the loader
# across a PCI-to-PCI bridge; it is backed by a 64 MiB sparse raw image created once in the build output directory.
# The loader reports every assigned memory BAR and maps none: every function starts unowned, dom0 claims the ones it
# uses (sys_pci_claim) and a process maps BAR0 of a function it owns with map_pci_bar_4k/2m at 0xd0_0000_0000 + physical
# address (boot/dom0-bench/src/bar.rs).
# `+invtsc` makes the TSC rate known to QEMU, which then reports it in the hypervisor leaf 4000_0010H that the NVMe
# benchmark reads when the host CPU has no CPUID leaf 16H.
# NVME_BLOCK_SIZE=4096 (default 512) formats the emulated NVMe namespace with that logical block size.
# VERIFLAT_PARALLEL picks the parallel timings of a NO_TIMER dom0 (see boot/bench/README.md).
set -euo pipefail
cd "$(dirname "$0")/.."

PROFILE=${PROFILE:-release}
BUILD_FEATURES=()
if [ -n "${NO_TIMER:-}" ]; then BUILD_FEATURES+=(--features kernel/no-timer,dom0-bench/no-timer); fi
if [ "${DMA_WRITE_TEST:-0}" = 1 ]; then BUILD_FEATURES+=(--features dom0-bench/dma-write-test); fi
# The E810 benchmarks place thread k on CPU k by bringing CPU k online to pull it, which a timer tick on CPU 0 can
# preempt into pulling dom0's first thread instead: their kernel runs without the timer.
if [ "${ICE_BENCH:-0}" = 1 ]; then BUILD_FEATURES+=(--features kernel/no-timer,dom0-bench/ice-bench); fi
if [ "${ICE_XPROC:-0}" = 1 ]; then BUILD_FEATURES+=(--features kernel/no-timer,dom0-bench/ice-xproc); fi
if [ "${ICE_MOCK:-0}" = 1 ]; then BUILD_FEATURES+=(--features kernel/no-timer,dom0-bench/ice-mock); fi
if [ "${ICE_CHAN_MOCK:-0}" = 1 ]; then BUILD_FEATURES+=(--features kernel/no-timer,dom0-bench/ice-chan-mock); fi
if [ "${PAYLOAD_PATH:-0}" = 1 ]; then BUILD_FEATURES+=(--features dom0-bench/payload-path); fi
cargo +1.99.1 build --profile "$PROFILE" -p aloader -p kernel -p dom0-bench "${BUILD_FEATURES[@]}"
OUT=target/x86_64-unknown-none/$PROFILE

[ -f "$OUT/nvme.img" ] || qemu-img create -q -f raw "$OUT/nvme.img" 64M

JUMBO=$(mktemp --suffix=.veriflat-jumbo)
trap 'rm -f "$JUMBO"' EXIT
cat "$OUT/kernel" "$OUT/dom0-bench" > "$JUMBO"

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
