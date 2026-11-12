# dom0 timing benchmarks

Drivers for the TSC timings dom0 prints under KVM. Results and images go to `boot/bench/out/`
(gitignored). All numbers are TSC cycles.

## Build modes

- `boot/run.sh`: the full dom0 test with the LAPIC timer. It prints the null syscall, mmap, IPC,
  intra-process call, and new_thread timers on the way.
- `NO_TIMER=1 SMP=n boot/run.sh`: kernel and dom0 with feature `no-timer`. dom0 runs only the timers
  (adding the parallel call and cross-process call timers) and exits. Use this mode for measurements.
  `VERIFLAT_PARALLEL` of the dom0 build picks the parallel timings, a comma-separated list of `call`
  (default), `mmap` (the parallel mmap timing), `mmap2m` (the parallel mmap_2m timing), and `unmapn`
  (dom0 alone: `unmapn <4k|2m> n=..` lines, median cycles of an n-page unmap and of the re-touch of a
  128-page working set right after it), and `mmap1g` (dom0 alone: one `mmap1g:` line, the median cycles of
  `mmap_1g` of one 1 GiB page, which zeroes it, of the `unmap_1g` after it, and of their sum, with the
  min and max of the sum; skipped when the boot found no free 1G block).
- `VERIFLAT_BOOT_2M_BLOCKS=n` of the kernel build (decimal, default 4) sets the free 2M blocks the kernel
  hands to the 2M allocator at boot, which are the root container's 2M quota. `build-parallel-call-image.sh`
  sets it to 128 (256 MiB of the managed GiB) unless `BOOT_2M_BLOCKS` says otherwise; `boot/run.sh` passes
  it through from the environment.

QEMU exits with status 1 when dom0 passed (isa-debug-exit maps code 0 to 1).

## Scripts

- `build-parallel-call-image.sh [out_dir]`: builds the no-timer image as `NO_TIMER=1 boot/run.sh`
  does and stores `aloader`, `jumbo` (kernel ELF then dom0 ELF), and `built-from.txt` (commit, dirty
  `src/` and `boot/` files, parallel timings, hashes) in `out_dir`, default `out/image`.
  `WORKTREE=<checkout>` builds another checkout, such as a `git worktree add` of a baseline commit or
  an `export-snapshot.sh` export. `PARALLEL` sets `VERIFLAT_PARALLEL` (default `call`), `BOOT_2M_BLOCKS`
  sets `VERIFLAT_BOOT_2M_BLOCKS` (default 128); `built-from.txt` records both.
- `export-snapshot.sh <snap_dir> [commit]`: exports a commit (default `HEAD`) without git metadata,
  with `verus` linked to this checkout's, so an image can be built from a fixed kernel while `src/` is
  being edited. `OVERLAY="<path>..."` copies working-copy files over it (such as an uncommitted
  `boot/dom0/src/main.rs`); `SNAPSHOT_OF` records both and lands in `built-from.txt`.
- `run-parallel-call.sh <runs> <smp>...`: boots the stored image `runs` times at each SMP count with
  `taskset -c 0-31`, KVM, `-cpu host`, `q35,kernel_irqchip=split`, `-m 6144 -mem-prealloc` (`MEM=<MiB>` overrides 6144), and
  isa-debug-exit, each under a 300 s `timeout`. Per run it appends the status to `status.txt` and the
  timer lines to `extracted.txt` in `OUT` (default `out/results`) and deletes the raw log of a passing
  run. `IMAGE` picks the image; `B_IMAGE` (and `B_OUT`, default `out/results-b`) turns on A/B mode;
  `FIRST_RUN` numbers further runs into the same directories.
- `summarize-parallel-call.py <results_dir>...`: over the passing runs of each directory, per SMP the
  median, min, and max of every timer, and the parallel call table of the median run with the ranges
  across runs. Run it with `python3 -I`.
- `summarize-parallel-mmap.py <results_dir>...`: the parallel mmap timing over the passing runs: per
  mode and SMP the medians across runs of each run's median alone and concurrent cycles per round and
  of its median ratio, the concurrent cycles over the SMP=1 alone cycles (`vs smp1`), and the overlap
  range with the number of runs that reached 0.50 (runs below it are left out of the medians unless
  none reached it). The parallel mmap_2m modes come in TSC cycles per 2 MiB, followed by a table of each
  2M variant against its 4K twins. Run it with `python3 -I`.

## Timer lines

| line | what it times |
| --- | --- |
| `null syscall: A TSC cycles returning through sysretq, B through iretq` | one `debug_null` syscall per return path; best of 5 interleaved rounds of 100,000 calls |
| `mmap 4K: N TSC cycles per page, K pages per call, over 16384 pages` | `mmap_4k` and a touch of 16384 fresh pages in an unmapped GiB, page tables included, with 64 pages per call and with 1 |
| `mmap+unmap 4K: N TSC cycles per page over 1000 rounds` | one `mmap_4k` of 64 fresh pages, a touch of each, and one `unmap_4k`, page tables already built; mean per page |
| `IPC round trip: N TSC cycles (4 syscalls, 2 thread switches)` | `send_empty` then `receive_empty` against a pong thread of dom0 |
| `call round trip: N TSC cycles (2 syscalls, 2 direct switches)` | `call_usize` answered by `reply_and_receive_usize` of a server thread in dom0 |
| `call round trip cross process: N TSC cycles (...)` | the same with the server in a child process, so each switch loads the other cr3; after 100 untimed rounds; no-timer only |
| `new_thread: best B TSC cycles, mean M over 32 threads` | `new_thread` of a thread that only yields |
| `parallel_call cpu=k alone=A conc=C ratio=R` | one call pair per CPU: round trip cost of pair k timed alone while the other clients spin, and with all pairs at once, over a 100M-cycle window; `ratio` = conc / alone; no-timer only |
| `parallel_call summary n=... median_ratio=... overlap=...` | ratios across CPUs, and the share of the concurrent span in which every pair was timing; dom0 fails below 0.50 |
| `parallel_call_xproc cpu=k ...`, `parallel_call_xproc summary ...` | the same two lines after them, with each server the first thread of a child process sharing dom0's image (own endpoint, killed afterwards), so every round trip also loads both cr3s; `parallel_call_xproc funding` gives the 4K quota per pair and how many pairs it covers; `summarize-parallel-call.py` skips these lines |

A ratio near 1.00 means the pairs do not slow each other down through the kernel. At most 24 pairs are timed, also at SMP 32, because pair k uses dom0 descriptor 8 + k, which must stay below the 32 endpoint descriptors of a thread; the parallel mmap and mmap_2m workers are these pairs' clients, so the same cap applies to them.

## Parallel mmap timing

Built with `PARALLEL=mmap` (or `call,mmap`). The parallel call timing's clients are the workers: worker
k runs on CPU k, worker 0 is dom0 itself. Each mode times every worker alone (the other workers spin in
user space) over a 100M-cycle window, then all at once until one shared deadline: 100M cycles, or
longer (up to 2G) when a round is so slow that 32 rounds of every worker taken in turn would not fit.
Alone, a worker runs 16 untimed rounds first and at least 8 timed rounds. A round maps one 4K page
(`mmap_4k(va, 1)`), writes and reads it, and in the map+unmap modes unmaps it (`unmap_4k(va, 1)`).
Between rounds, untimed and left out of the cycles per round, a worker moves 512 4K quota to its
thread when it runs low (`alloc_quota_4k` + `alloc_thread_quota_4k`), and in the mmap-only modes
unmaps its whole region once full (or early, when the container runs out of quota). The overlap
condition is the call timing's, but a mode below 0.50 is only logged as an error and the run goes on.

| mode (line prefix) | workers | region of worker k |
| --- | --- | --- |
| `parallel_mmap_same` | threads of dom0, map+unmap | one page in its own 2M window at `0xc0_8000_0000 + k * 16M` (each worker's L2 entry in its own cache line) |
| `parallel_mmap_only_same` | threads of dom0, mmap-only | 2048 pages (four 2M windows) at `0xc0_c000_0000 + k * 16M` |
| `parallel_mmap_xproc` | the first thread of one child process per worker (sharing dom0's image, own page table and PCID, same container), map+unmap | as `parallel_mmap_same`, in its own address space |
| `parallel_mmap_only_xproc` | the same children, mmap-only | as `parallel_mmap_only_same` |
| `parallel_mmap_cached_xproc` | the same children, mmap-only with a 128-page region | after the first region unmap its pages stay in the per-CPU page cache (it drains to the global pool only at 4096 pages), so no round touches the global pool; a diagnostic of the pool's cost |

Lines: `<prefix> cpu=k alone=A conc=C ratio=R` and `<prefix> summary ...` as for the parallel call
timing, now in cycles per round; `parallel_mmap_xproc funding` as `parallel_call_xproc funding` (the
children are killed after the cross-process modes); `<prefix> quota: region P pages per worker, S early
region unmaps for want of container quota` after each mmap-only mode. In the same-process modes the
alone value already contains what the other CPUs cost: each unmap flushes the TLB of every CPU that
runs dom0, the spinning workers included; `vs smp1` compares with an SMP=1 run instead.

Run: `PARALLEL=mmap boot/bench/build-parallel-call-image.sh boot/bench/out/image-mmap`, then
`IMAGE=boot/bench/out/image-mmap OUT=boot/bench/out/results-mmap boot/bench/run-parallel-call.sh 7 1 4 8 16 32`
(every run boots each SMP count in turn), then
`python3 -I boot/bench/summarize-parallel-mmap.py boot/bench/out/results-mmap`.

## Parallel mmap_2m timing

Built with `PARALLEL=mmap2m` (or with it in a list). It needs the kernel's `mmap_2m` and `unmap_2m`
(syscalls 47 and 48) and enough 2M quota: each worker uses at most 8 2M pages at a time and moves back
what its thread still holds after every phase, so the default image's 128 blocks cover 16 workers. The
workers and the alone and concurrent windows are those of the parallel mmap timing, first threads of dom0
(`_same`), then the first threads of one child process per worker (`_xproc`). Every round handles 2 MiB,
as 2M pages or as 4K pages, with the same touch (one write per 4K page, the last read back) and the same
untimed funding (4K quota 2048 at a time, but for a whole region's map no more than is missing, and just
what is missing once the container holds less; 2M quota topped up to 8). After the last `_same` phase
dom0's worker threads map and unmap the 4K quota they still hold, which gives it back to the container for
the children. Every line gives TSC cycles per 2 MiB.

| line prefix (`_same` / `_xproc`) | a round, timed | untimed |
| --- | --- | --- |
| `parallel_mmap2m_mapunmap_2m` | `mmap_2m(va, 1)`, touch, `unmap_2m(va, 1)` | |
| `parallel_mmap2m_mapunmap_4k` | `mmap_4k(va, 512)`, touch, `unmap_4k(va, 512)` | |
| `parallel_mmap2m_mapunmap_4k1` | 512 × `mmap_4k(va + 4K·i, 1)`, touch, `unmap_4k(va, 512)` | |
| `parallel_mmap2m_mmaponly_2m` | `mmap_2m` of the next 2 MiB of an 8 × 2M region, touch | region unmap once full |
| `parallel_mmap2m_mmaponly_4k` | `mmap_4k(…, 512)` of the next 2 MiB of a 4096-page region, touch | region unmap once full |
| `parallel_mmap2m_unmaponly_2m` | `unmap_2m(base, 8)` | `mmap_2m(base, 8)`, touch |
| `parallel_mmap2m_unmaponly_4k` | `unmap_4k(base, 4096)` | 8 × `mmap_4k(…, 512)`, touch |

Regions: worker k at `k * 16M` in its kind's GiB, the 2M variants in `0xc1_0000_0000`, `0xc1_4000_0000`,
`0xc1_8000_0000` and the 4K twins in `0xc2_…` at the same offsets, so no 2M window ever holds an L1
table. dom0 builds the directories of its GiBs first, with `mmap_2m` + `unmap_2m` in the 2M ones. Other
lines: `parallel_mmap2m_xproc funding` and, after each mmap-only mode, `<prefix> quota: ...` as for the
parallel mmap timing.

The map+unmap and mmap-only modes also split each timed round into separate TSC windows: after the
combined lines of a prefix (such as `parallel_mmap2m_mmaponly_2m_same`) come the same lines with
`_syscall` appended (the map and unmap calls) and with `_touch` appended (the touch), over the same rounds. The summary's last table lists alone / conc
and the ratio of the combined, syscall, and touch parts per mode.

Run: `PARALLEL=mmap2m boot/bench/build-parallel-call-image.sh boot/bench/out/image-mmap2m`, then
`IMAGE=boot/bench/out/image-mmap2m OUT=boot/bench/out/results-mmap2m boot/bench/run-parallel-call.sh 5 1 2 4 8 16`,
then `python3 -I boot/bench/summarize-parallel-mmap.py boot/bench/out/results-mmap2m`.

The timer build of dom0 also runs a functional test of `mmap_2m` and `unmap_2m` after its first mmap test
(`mmap_2m self-test passed`), or logs `mmap_2m self-test skipped` while the kernel answers syscall 47 with
InvalidSyscall.

## mmap_1g timing

Built with `PARALLEL=mmap1g` (or with it in a list); run it at SMP 1:
`PARALLEL=mmap1g boot/bench/build-parallel-call-image.sh boot/bench/out/image-mmap1g`, then
`MEM=2304 IMAGE=boot/bench/out/image-mmap1g OUT=boot/bench/out/results-mmap1g boot/bench/run-parallel-call.sh 3 1`
(the default `-m 6144` puts q35's ACPI tables just below 2 GiB, so the boot finds no free 1G block),
then `grep mmap1g: boot/bench/out/results-mmap1g/extracted.txt`. The kernel build's free 1G block
(`VERIFLAT_BOOT_1G_BLOCKS`, default 1, [1 GiB, 2 GiB)) needs CPUID pdpe1gb, which `-cpu host` passes
through when the host has it. The map time is dominated by zeroing the 1 GiB page inside the leaf step,
with interrupts off on that CPU and the page table write-locked; divide by the TSC rate for wall time.

The timer build also runs a functional test of `mmap_1g`, `unmap_1g`, and the 1G quota calls after the
mmap_2m test (`mmap_1g self-test passed`), or logs `mmap_1g self-test skipped` while the kernel answers
syscall 49 with InvalidSyscall or when the root container has no 1G quota.

## Interleaved A/B protocol

1. Build both images: `WORKTREE=<baseline checkout> boot/bench/build-parallel-call-image.sh boot/bench/out/image-a`
   and `boot/bench/build-parallel-call-image.sh boot/bench/out/image-b`.
2. Run them interleaved, 5 runs each:
   `IMAGE=boot/bench/out/image-a OUT=boot/bench/out/results-a B_IMAGE=boot/bench/out/image-b B_OUT=boot/bench/out/results-b boot/bench/run-parallel-call.sh 5 4`.
   Every run boots A, then B, so host drift hits both alike.
3. Every run must exit with status 1. Compare the medians over the 5 runs:
   `python3 -I boot/bench/summarize-parallel-call.py boot/bench/out/results-a boot/bench/out/results-b`.

## NVMe driver benchmark (port of Atmosphere's)

The timer build of dom0 runs a port of Atmosphere's user-level NVMe driver and benchmark
(`boot/dom0/src/nvme/`, `boot/dom0/src/slab_alloc.rs`) after the kill tests, against the emulated
`-device nvme` that `boot/run.sh` attaches behind a PCIe root port (64 MiB raw image). It finds the controller
with `pci_info` (class 01, subclass 08, on any bus: the loader scans all 256 buses, so that the root buses of a server's further host bridges and the buses behind PCI-to-PCI bridges are covered), drives it by polling through BAR0 at `0xd0_0000_0000 + base`, and
maps every DMA buffer at IOVA = VA (`mmap_4k` + `iommu_map_4k` in the heap's pager). Without an NVMe
function it logs `nvme bench skipped`. Each run is sequential 4 KiB I/O (8 LBAs per request) for 2 s;
`VERIFLAT_NVME_SECS=30 boot/run.sh` builds dom0 with 30 s runs, the thesis's length.

Configurations, in this order, each with read and write at submission batch 1 and 32:

| line | configuration | sample |
| --- | --- | --- |
| `nvme linked <op> batch=b` | the driver in dom0's own thread (`run_blocktest_raw_with_delay`) | one `submit_and_poll_raw` call that submitted or reaped a request |
| `nvme ipc <op> batch=b` | the driver in a child process on CPU 0; dom0 fills up to b requests into a shared ring and `call`s it once per batch, the driver submits and reaps once and answers with `reply_and_receive` | one round: ring update plus the call |
| `nvme twocore <op> batch=b` | the same driver process polling the ring on CPU 1 while dom0 spins on CPU 0 | cycles between two client rounds that moved a request |

Each line reads `nvme <config> <read|write> batch=<b>: <iops> IOPS, <n> completed in <ms> ms, <sample> median
<c> min <c> max <c> TSC cycles over <rounds> rounds`; IOPS use the TSC rate that `nvme: TSC <MHz> MHz from
<source>` names: `VERIFLAT_TSC_MHZ` of the dom0 build if set, else CPUID 16H, else the hypervisor leaf 4000_0010H,
else the "@ x.xxGHz" end of the CPUID brand string; with none of these the benchmark fails. As in
Atmosphere, the batch is how many requests a round submits, not a queue depth: the linked client allocates a
new batch whenever no request waits, and the ring clients push whenever a ring buffer is free, so up to 1023
(linked) or 1024 (ring) requests are in flight at batch 1 too; only `ipc` at batch 1 stays near one request
per call. The child is killed after each ring configuration, which returns the function to dom0.

Measured 2026-11-11, QEMU-emulated NVMe (not a real device: every doorbell is a VM exit into QEMU, which
caps the rate near 75K IOPS), KVM on the i9-13900HX, TSC 2419 MHz from the hypervisor leaf, 2 s runs, `boot/run.sh`
(SMP 4) / `SMP=16 boot/run.sh`:

| configuration | read b=1 | read b=32 | write b=1 | write b=32 |
| --- | --- | --- | --- | --- |
| linked, IOPS | 72.9K / 75.6K | 54.0K / 56.8K | 72.1K / 78.1K | 54.3K / 51.5K |
| linked, median cycles per call | 1.03M / 1.11M | 18.8K / 20.2K | 1.04M / 1.84M | 19.7K / 18.7K |
| ipc, IOPS | 18.9K / 18.8K | 69.4K / 74.4K | 18.3K / 18.9K | 71.1K / 74.3K |
| ipc, median cycles per round (call included) | 129K / 126K | 703 / 1.03M | 127K / 125K | 1.06M / 1.03M |
| twocore, IOPS | 69.3K / 72.6K | 71.0K / 72.8K | 70.6K / 71.9K | 71.3K / 73.3K |
| twocore, median cycles between rounds | 45 / 45 | 1.04M / 1.02M | 45 / 45 | 1.05M / 1.03M |

These numbers measure QEMU's device model more than the driver or the kernel; they are not comparable with
the thesis's real-device figures (Atmosphere reaches the SSD's maximum read rate and 232K IOPS on
sequential writes at batch 32).

### Real hardware

Not yet tried on a real machine. The target is a CloudLab d430 (2x Xeon E5-2630 v3, Haswell: no RDPID, no
CPUID leaf 16H; the NVMe SSD sits behind a PCIe root port). The machine needs VT-d on, and the firmware must place
the SSD's BAR0 below 4 GiB (turn above-4G decoding off): the loader moves a 64-bit BAR0 only on bus 0, and on any
other bus it skips an NVMe, Ethernet or `edu` function whose BAR0 is unassigned or not below 4 GiB with a warning
that names the function, so that such a device stays out of dom0 but does not stop the boot.

The GRUB `multiboot2` path below has been booted under QEMU (KVM, q35, the devices of `boot/run.sh`) and passes
the NVMe benchmark and the dom0 tests: from a `grub-mkrescue` ISO with GRUB 2.12 on SeaBIOS, with `serial=com2`
too (the loader's and the kernel's output then arrive on the second serial port; only the loader's first lines
and one kernel line printed before the kernel reads its command line stay on COM1), and from a standalone GRUB 2.14
x86_64-efi image on OVMF, where the loader takes the RSDP from GRUB's ACPI tags since UEFI has none in the BIOS
area. Untried on hardware: the server's firmware memory map, ACPI tables, VT-d units and serial ports, GRUB as
installed on the server's disk, and the real SSD.

1. Build with 30 s runs: `cd boot && VERIFLAT_NVME_SECS=30 cargo +1.99.1 build --profile release -p aloader -p kernel -p dom0`.
   The E5-2630 v3 has no leaf 16H, so outside a hypervisor dom0 takes the TSC rate from the brand string's
   "@ 2.40GHz"; `VERIFLAT_TSC_MHZ=<MHz>` in the same build overrides it. Concatenate the kernel and dom0 as
   `boot/run.sh` does, `cat kernel dom0 > veriflat-jumbo` in `boot/target/x86_64-unknown-none/release/`, and copy
   `aloader` and `veriflat-jumbo` to `/boot`.
2. Add a GRUB entry, with `serial=com2` on the `multiboot2` line if the console is COM2. This is the entry that
   booted under QEMU (there the module file was named `/boot/jumbo`), with GRUB itself on the serial console
   (`--unit=1` for COM2) and no menu wait:

   ```
   serial --unit=0 --speed=115200
   terminal_input serial
   terminal_output serial
   set timeout=0
   menuentry "VeriFlat" {
       multiboot2 /boot/aloader
       module2 /boot/veriflat-jumbo
   }
   ```

3. Read the result lines from the serial console; the loader and the kernel use COM1 unless the boot command line
   has `serial=com2` (or `com3`, `com4`). At the end dom0 writes its status to QEMU's exit port, which does nothing
   on a real machine, so the machine then stays up until it is reset.

#### Unattended runs with a RAM log

When nobody can read the serial console, the boot option `ramlog=<hex physical address>` makes the loader, the
kernel and dom0's output also go to a 16 MiB RAM buffer at that address (at or above 4 GiB, 2 MiB aligned, inside
one 1 GiB region). The buffer starts with a 4 KiB header (magic `VFRAMLOG`, version, capacity, bytes written,
exit reason and code; `boot/ns16550a/src/ramlog.rs`); writes stop when it is full. With the option, dom0's
`sys_debug_exit(code)`, a kernel or loader panic and a fatal kernel exception record the reason and code, write
back the caches and warm-reset the machine (port 0xCF9, then the keyboard controller). `reset_after=<seconds>`
also resets the machine (reason "timeout") at the first timer tick after that many seconds from kernel start, with
the TSC rate from CPUID 16H or 4000_0010H, or 3 GHz assumed when neither gives one (an E5-2630 v3 at 2.4 GHz then
waits 25% longer). Without `ramlog=` every end behaves as before.

The boot option `maxcpus=<n>` makes the loader hand only the first n processors of the ACPI MADT list to the kernel,
so that the kernel and dom0 see n CPUs; the loader logs "maxcpus=n: using n of m processors" and ignores n = 0 and
an n above the count. The loader also reads the boot command line from the PVH start info, so under QEMU it comes
from `-append`, e.g. `NO_TIMER=1 SMP=8 boot/run.sh -append maxcpus=2`.

1. Keep the buffer out of Linux's memory with the kernel parameter `memmap=16M!0x140000000` (in
   `GRUB_CMDLINE_LINUX` of `/etc/default/grub`, then `update-grub`); Linux then shows it as `/dev/pmem0`.
2. Add the VeriFlat entry and, with `GRUB_DEFAULT=saved`, boot it once with `grub-reboot "VeriFlat"`, so that the reset returns to Linux:

   ```
   menuentry "VeriFlat" {
       multiboot2 /boot/aloader ramlog=0x140000000 reset_after=600
       module2 /boot/veriflat-jumbo
   }
   ```

3. Back in Linux, read the log: `sudo python3 boot/tools/ramlog_read.py /dev/pmem0`. It prints the header (the
   exit reason "running" means the machine reset without recording an end) and the text, and exits with status 1
   when the magic is missing, as when the RAM did not survive the reset or Linux overwrote it.

Tested under QEMU/KVM only (GRUB ISO, `-m 8192`, the dump taken with QMP `pmemsave` after the reset): the dump
holds the loader's lines from its banner on, the kernel's, dom0's `dom0 test passed` and exit reason
`sys_debug_exit` with code 0; the loader-panic and `reset_after` ends record their reasons too. Whether the
server's RAM keeps its contents across the warm reset is untested.

Warning: the benchmark writes the SSD from LBA 0 on. It destroys whatever the SSD holds, partition table included,
so never run it on a machine whose NVMe SSD has data.

## E810 (ice) driver benchmark

A polling, multi-queue user-level driver for the Intel E810 (PCI 8086:1591..1593 E810-C, 1599..159b E810-XXV), for
throughput scaling with cores on a CloudLab c6620. Nothing of it has run on an E810 yet: no such device or QEMU model
was available, so it is built and reviewed against the Linux `ice` headers (read as a reference) and tested on a
software device model only.

- `boot/ice/`: the hardware-independent core (no_std). Its only hardware access is the `Platform` trait (32-bit BAR0
  read/write, zeroed DMA allocation returning VA and IOVA, delay, TSC). `Device::new` does a PF reset, the control
  queue bring-up (retried while the firmware does not answer), Get Version, Clear PF Configuration, Clear PXE Mode,
  List Function Capabilities, Get Switch Configuration (logical port, switch ID), Manage MAC Read, Query Scheduler
  Resource Allocation and Get Default Topology, removal of the firmware's default scheduler nodes from the entry point
  layer down, a chain of scheduler nodes and enough queue group nodes for N queues, Add VSI (one PF VSI, N contiguous
  queues, PF RSS table, Toeplitz), Add Tx LAN Queues, Rx queue contexts through `QRX_CONTEXT` with RXDID 2 (32-byte
  flex descriptors) and the queue enables, Set RSS Key and LUT, the Rx switch rules, and `bring_link_up` (Get Link
  Status, Restart Autonegotiation with the link enabled). `bench::run_queue_pair` is the loop both front ends run.
- `boot/ice-linux/`: a host program (own workspace, builds into `boot/target/x86_64-unknown-linux-gnu`) that runs the
  core from Linux user space, ixy-style: BAR0 through sysfs `resource0`, DMA memory from 2 MiB hugepages with physical
  addresses from `/proc/self/pagemap`, one pinned thread per queue pair. `ice-linux` without arguments prints its
  options.
- `boot/dom0/src/ice_bench.rs`: the dom0 front end, built with feature `ice-bench` (`ICE_BENCH=1 boot/run.sh`). It runs
  first and alone, finds the E810 with `sys_pci_info` (`VERIFLAT_ICE_BDF=bb:dd.f`, else the first E810-C, else the
  first E810), attaches it with `pci_attach_dma`, drives BAR0 at `0xd0_0000_0000 + base` and takes DMA memory from
  the heap (IOVA = VA). Worker k runs on CPU k (placed as the parallel call timing places its clients) and owns
  queue pair k. Build-time settings: `VERIFLAT_ICE_SECS` (5), `VERIFLAT_ICE_QUEUES` (one per CPU),
  `VERIFLAT_ICE_FRAME` (64, with CRC), `VERIFLAT_ICE_MODE` (`tx`, `rx`, `both`, default `both`), `VERIFLAT_ICE_DST` or
  `VERIFLAT_ICE_PEER` (+ `VERIFLAT_ICE_PEER_QUEUES`), `VERIFLAT_ICE_STEER` (`mac`, `promisc`), `VERIFLAT_ICE_LINK_SECS`
  (15). Without an E810 it logs `ice bench skipped: no E810 function recorded`; the default dom0 test logs the same, or
  the E810 functions the loader recorded.

Each queue sends one fixed UDP frame (one descriptor per frame, all pointing at the same buffer, report status on the
last of each 32-descriptor batch) and counts what its Rx queue receives (buffers re-armed in place). The result lines
are `ice queue <q> cpu <q>: tx <pps> pps, rx <pps> pps, rx errors <n>`, `ice total: tx .. pps, rx .. pps over <n>
queues; line rate of <s>-byte frames at <Mb/s> is <pps> pps`, and `ice port: ..` with the port counters over the run
(`GLPRT_*`); the Linux program prints the same without the `ice` prefix.

Receive spreading. RSS hashing on E810 needs the DDP package downloaded to the device and RSS flow profiles programmed
through it (the Linux driver's `ice_flex_pipe`/`ice_flow` code); without a package the Linux driver runs in "safe mode"
with one queue. That is not implemented: the VSI gets a PF lookup table and a key, but the device computes no hash.
Frames reach queue q instead through switch rules: frames to the steering MAC `02:b2:b3:b4:b5:qq` (bytes 2..5 of the
port's MAC, then q) go to queue q, frames to the port's own MAC to the VSI. A peer running the same benchmark with
`--peer <this port's MAC>` (`VERIFLAT_ICE_PEER`) sends queue q's frames to this side's queue q. `--steer promisc`
(`VERIFLAT_ICE_STEER=promisc`) instead installs the default-VSI rule, which takes every frame into the VSI (one queue
without a hash). If the firmware refuses the Rx MAC rules the driver falls back to the default-VSI rule and says so.

Checked here: `cd boot && cargo +1.99.1 test -p ice --target x86_64-unknown-linux-gnu` (descriptor, context, admin
command, VSI, switch rule and scheduler layouts; ring arithmetic; the UDP frame and IPv4 checksum; and a software model
of the PF that runs the whole bring-up, checks every DMA address against the driver's allocations, and loops frames
through the Tx queues, the steering rules and the Rx queues); the bare-metal build of `ice` and `dom0` with and without
`ice-bench`; the Linux program's build and argument handling; `boot/run.sh` and `ICE_BENCH=1 boot/run.sh` under KVM
with SMP 4, both passing with the skip line. The device model encodes the same reading of the specification as the
driver, so it finds plumbing errors, not misreadings.

Untested on hardware, each following the Linux driver's encoding of the datasheet topic named:

| part | topic | what may differ |
| --- | --- | --- |
| PF reset, reset-done wait (`PFGEN_CTRL.PFSWR`, `GLGEN_RSTAT`, `GLNVM_ULD`) | resets | timing after UEFI/UNDI or after Linux's `ice` |
| control queue registers, descriptor flags, one 4 KiB buffer, head polling, ARQ re-posting | control queues | whether the firmware needs anything before the first command |
| Get Version, Clear PF Configuration (0x02A4), Clear PXE Mode, List Function Capabilities | admin commands | capability IDs and fields |
| Get Switch Configuration, Manage MAC Read | switch / MAC admin commands | which element is this PF's port |
| Query Scheduler Resources, Get Default Topology, Delete/Add Scheduler Elements | transmit scheduler | the default tree shape, which nodes may be deleted, children limits |
| Add VSI with the 128-byte properties block (firmware-chosen VSI number) | VSI configuration | valid-section bits on add, VSI number allocation |
| Add Tx LAN Queues with the 22-byte Tx queue context | transmit queue context | context fields (TSO queue, legacy interrupt, timestamp enable as Linux sets) |
| Rx queue context through `QRX_CONTEXT`, `QRXFLXP_CNTXT` RXDID 2, `QRX_CTRL` enable | receive queue context | none expected; the context layout is checked by tests |
| Tx data descriptor (EOP, RS per batch, done = DTYPE 0xF), flex Rx write-back (DD, EOF, RXE, length) | descriptors | none expected |
| Set RSS Key / Set RSS LUT (PF table, 2048 entries) | RSS | inert without a DDP package |
| Rx lookup switch rules: MAC (recipe 1) to queue / to VSI, default (recipe 5) to VSI | switch rules | whether Rx MAC rules are accepted (the Linux driver adds MAC filters as Tx rules); queue index device-wide (`rxq_first` + q) |
| Get Link Status (32-byte buffer), Restart Autonegotiation | link | whether a down link needs Set PHY Config first |
| `GLPRT_*` port counters | statistics | counter latching |
| dom0: worker placement on CPUs coming online, heap DMA at IOVA = VA above 4 GiB, BAR0 window as UC through MTRRs | VeriFlat | untested with any NIC |

Kernel and loader gaps (nothing changed for them):

- BAR0 placement: the E810's BAR0 is a 64-bit prefetchable BAR (32 MiB on the E810-C: Atmosphere's c6620 run found
  it at 0xfa000000, size 0x2000000). The loader records a function off bus 0 only when the firmware placed BAR0 below
  4 GiB, because io pages must lie in the page array, which covers [0, 4 GiB); with above-4G decoding on (usual on UEFI
  servers) the E810 is skipped with a warning. Turn above-4G decoding off, or the page array and loader must learn
  BARs above 4 GiB (a kernel and model change). The loader also panics unless the MTRRs make BAR0 uncacheable.
- No MSI-X or interrupts are needed (polling); BAR3 (MSI-X table) stays unmapped. No new syscall is needed.
- At most 16 recorded functions (`MAX_PCI_DEVICES`); a c6620 has 2 + 2 E810 ports plus NVMe and other NICs.
- 40 CPUs at most; boot with `maxcpus=` on a machine with more logical processors.

On the real machine, Linux front end first:

1. Find the cabled 100G port: `lspci -nn | grep -i e810`, `ip -br link`, `ethtool <if>`; note its PCI address and
   MAC on both nodes (the program prints the MAC at bring-up too).
2. Boot Linux with `intel_iommu=off` (or `iommu=pt`), since the program hands physical addresses to the device, and
   reserve hugepages: `echo 512 | sudo tee /proc/sys/vm/nr_hugepages`.
3. Build: `cd boot/ice-linux && cargo +1.99.1 build --release` (the binary is `boot/target/x86_64-unknown-linux-gnu/release/ice-linux`).
4. Unbind the port from `ice`: `echo <bdf> | sudo tee /sys/bus/pci/drivers/ice/unbind`.
5. Receiver on node B: `sudo ice-linux <bdf> --queues 8 --cpus 0-7 --mode rx --secs 10`; sender on node A:
   `sudo ice-linux <bdf> --queues 8 --cpus 0-7 --mode tx --peer <B's MAC> --secs 10`. Repeat with 1, 2, 4, ...
   queues on both sides for the scaling curve, and `--frame 1518` for the byte rate. Each run ends with a PF reset;
   rebind afterwards with `echo <bdf> | sudo tee /sys/bus/pci/drivers/ice/bind`.
6. If the bring-up stops, the log names the admin command and firmware return value; fix that in `boot/ice` and rerun.

Then dom0, once the Linux program works:

1. In the firmware setup: VT-d on, above-4G decoding off; check in Linux that `lspci -vv -s <bdf>` shows Region 0
   below 4 GiB.
2. Build: `cd boot && VERIFLAT_ICE_SECS=10 VERIFLAT_ICE_PEER=<peer MAC> VERIFLAT_ICE_MODE=both cargo +1.99.1 build
   --profile release -p aloader -p kernel -p dom0 --features dom0/ice-bench`, then concatenate kernel and dom0 into
   the jumbo image and boot it from GRUB as in the NVMe section above (`maxcpus=<n>` for n queue pairs, and the RAM
   log for unattended runs). The peer runs the Linux program (`--mode rx --peer <this port's MAC>` or `--mode both`).
3. Read the `ice queue`, `ice total` and `ice port` lines; `ice bench passed` ends the run.
