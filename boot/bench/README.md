# dom0 timing benchmarks

Drivers for the TSC timings the benchmark dom0 (`boot/dom0-bench`, branch `bench`) prints under KVM; `boot/run.sh`
boots main's small self-test dom0 instead. Results and images go to `boot/bench/out/`
(gitignored). All numbers are TSC cycles.

## Build modes

- `boot/bench/run.sh`: the full dom0 test with the LAPIC timer. It prints the null syscall, mmap, IPC,
  intra-process call, and new_thread timers on the way.
- `NO_TIMER=1 SMP=n boot/bench/run.sh`: kernel and dom0 with feature `no-timer`. dom0 runs only the timers
  (adding the parallel call and cross-process call timers) and exits. Use this mode for measurements.
  `VERIFLAT_PARALLEL` of the dom0 build picks the parallel timings, a comma-separated list of `call`
  (default), `mmap` (the parallel mmap timing), `mmap2m` (the parallel mmap_2m timing), and `unmapn`
  (dom0 alone: `unmapn <4k|2m> n=..` lines, median cycles of an n-page unmap and of the re-touch of a
  128-page working set right after it), and `mmap1g` (dom0 alone: one `mmap1g:` line, the median cycles of
  `mmap_1g` of one 1 GiB page, which zeroes it, of the `unmap_1g` after it, and of their sum, with the
  min and max of the sum; skipped when the boot found no free 1G block).
- `VERIFLAT_BOOT_2M_BLOCKS=n` of the kernel build (decimal, default 4) sets the free 2M blocks the kernel
  hands to the 2M allocator at boot, which are the root container's 2M quota. `build-parallel-call-image.sh`
  sets it to 128 (256 MiB of the managed GiB) unless `BOOT_2M_BLOCKS` says otherwise; `boot/bench/run.sh` passes
  it through from the environment.

QEMU exits with status 1 when dom0 passed (isa-debug-exit maps code 0 to 1).

## Scripts

- `build-parallel-call-image.sh [out_dir]`: builds the no-timer image as `NO_TIMER=1 boot/bench/run.sh`
  does and stores `aloader`, `jumbo` (kernel ELF then dom0-bench ELF), and `built-from.txt` (commit, dirty
  `src/` and `boot/` files, parallel timings, hashes) in `out_dir`, default `out/image`.
  `WORKTREE=<checkout>` builds another checkout, such as a `git worktree add` of a baseline commit or
  an `export-snapshot.sh` export. `PARALLEL` sets `VERIFLAT_PARALLEL` (default `call`), `BOOT_2M_BLOCKS`
  sets `VERIFLAT_BOOT_2M_BLOCKS` (default 128); `built-from.txt` records both.
- `export-snapshot.sh <snap_dir> [commit]`: exports a commit (default `HEAD`) without git metadata,
  with `verus` linked to this checkout's, so an image can be built from a fixed kernel while `src/` is
  being edited. `OVERLAY="<path>..."` copies working-copy files over it (such as an uncommitted
  `boot/dom0-bench/src/main.rs`); `SNAPSHOT_OF` records both and lands in `built-from.txt`.
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

## unmap_4k against the cpu set size

Built with `PARALLEL=unmapcpus` (alone, not in a list: dom0 runs only this timing, first, and exits; see
`boot/dom0-bench/src/unmap_cpus.rs`). It times `mmap_4k` and `unmap_4k` of one page, each call on its own (min,
median, and mean over 20,000 rounds after 2,000 warm-up rounds), page table window present, thread quota 16
so every unmap refunds to the thread, against the size of the caller container's cpu set, which `unmap_4k`'s
TLB flush walks. dom0's root thread times the root container's set of all 28 CPU ids (`NUM_CPUS`), then a helper thread
gives the ids away from 27 down, each as the transfer CPU of a new child container that never runs, and the
root thread times each smaller set down to {0}; ids at or above the kernel's `N CPUs present` have no
processor, the others are parked Off. Then CPU 1's child container is brought online and times the same
loop in its own process, cpu set {1}. Each container takes two 2M quota, so the kernel needs
`VERIFLAT_BOOT_2M_BLOCKS` >= 54 (`build-parallel-call-image.sh` sets 128; with `boot/bench/run.sh` pass
`NO_TIMER=1 VERIFLAT_PARALLEL=unmapcpus VERIFLAT_BOOT_2M_BLOCKS=128`).
Run: `PARALLEL=unmapcpus boot/bench/build-parallel-call-image.sh boot/bench/out/image-unmapcpus`, then
`IMAGE=boot/bench/out/image-unmapcpus OUT=boot/bench/out/results-unmapcpus boot/bench/run-parallel-call.sh 2 4`.

| line | what it gives |
| --- | --- |
| `unmapcpus calibration: empty rdtsc pair min A median B TSC cycles; compare_exchange + store C TSC cycles per iteration ...` | an empty rdtsc pair over 20,000 samples, and an uncontended `compare_exchange` plus a store on a cache-hot word, best of 5 × 1e6 |
| `unmapcpus root set=n ids=0..n-1 cpu=0: mmap_4k min .. median .. mean .., unmap_4k min .. median .. mean .. TSC cycles over 20000 rounds` | dom0's root thread with a root cpu set of n ids, n = 28 down to 1 |
| `unmapcpus child set=1 ids=1 cpu=1: ...` | the same loop in the child container on CPU 1 |
| `unmapcpus passed` | the end |

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
(`boot/dom0-bench/src/nvme/`, `boot/dom0-bench/src/slab_alloc.rs`) after the kill tests, against the emulated
`-device nvme` that `boot/bench/run.sh` attaches behind a PCIe root port (64 MiB raw image). It finds the controller
with `pci_info` (class 01, subclass 08, on any bus: the loader scans all 256 buses, so that the root buses of a server's further host bridges and the buses behind PCI-to-PCI bridges are covered), claims it (`pci_claim`: every function
starts unowned), maps BAR0 at `0xd0_0000_0000 + base` (`boot/dom0-bench/src/bar.rs`: `map_pci_bar_2m` when BAR0 is
2M-aligned and at least 2 MiB, `map_pci_bar_4k` otherwise), drives it by polling through it, and
maps every DMA buffer at IOVA = VA (`mmap_4k` + `iommu_map_4k` in the heap's pager). Without an NVMe
function it logs `nvme bench skipped`. Each run is sequential 4 KiB I/O for 2 s, 4 KiB of namespace 1's LBAs per
request (8 at 512-byte LBAs, 1 at 4 KiB LBAs; `nvme: LBA size ..` logs it after the linked configuration's Identify
Namespace, where Atmosphere always sends 8); an LBA size above 4 KiB logs `nvme bench skipped: namespace 1's LBA
size .. does not divide the 4 KiB request` and leaves the controller disabled, as does `parallel_nvme`.
`NVME_BLOCK_SIZE=4096 boot/bench/run.sh` formats the emulated namespace with 4 KiB LBAs (default 512);
`VERIFLAT_NVME_SECS=30 boot/bench/run.sh` builds dom0 with 30 s runs, the thesis's length.

Which drive: every NVMe test and benchmark of dom0 (this one, `parallel_nvme`, `parallel_nvme_xproc`) drives the one
function that `boot/dom0-bench/src/nvme/pci.rs` `selected_nvme` picks, and all of them write to it from LBA 0 on, destroying
its contents. `VERIFLAT_NVME_BDF=<bus>:<dev>.<fn>` of the dom0 build (hexadecimal, as `lspci` prints it, e.g.
`VERIFLAT_NVME_BDF=3c:00.0`) names it; without it, under a hypervisor (CPUID.01H:ECX bit 31) the recorded NVMe function
number `VERIFLAT_NVME_INDEX` in B/D/F order is used (default 0, the lowest B/D/F: `boot/bench/run.sh` behaves as before),
and on bare metal none is: before touching any controller each of them logs one line such as `nvme bench skipped: bare
metal and no NVMe function named; build dom0 with VERIFLAT_NVME_BDF=<bus:dev.fn> to pick one; recorded NVMe
functions: 3b:00.0 8086:0b60 3c:00.0 8086:0b60` (bus:dev.fn vendor:device; model and serial are not shown because
reading them needs an Identify command to the controller). A `VERIFLAT_NVME_BDF` that names no recorded NVMe function
skips them likewise. `VERIFLAT_NVME_ASSUME_BARE_METAL=1` makes dom0 take the bare-metal branch under QEMU too. On a
real machine, name the drive that holds nothing: find the boot disk with `findmnt /` and `lsblk`, and the PCI address
of each NVMe with `readlink /sys/class/nvme/nvme*/device` (`cloudlab_tools/node-check.sh` prints both).

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
per call. dom0 unmaps BAR0 before it sends the function to the driver process (a function cannot be sent while a BAR
page of it is mapped), and the driver process maps BAR0 itself. The child is killed after each ring configuration,
which leaves the function unowned; dom0 claims it again.

Measured 2026-11-11, QEMU-emulated NVMe (not a real device: every doorbell is a VM exit into QEMU, which
caps the rate near 75K IOPS), KVM on the i9-13900HX, TSC 2419 MHz from the hypervisor leaf, 2 s runs, `boot/bench/run.sh`
(SMP 4) / `SMP=16 boot/bench/run.sh`:

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

### Parallel NVMe benchmark (one queue pair per CPU)

`NO_TIMER=1 SMP=n VERIFLAT_PARALLEL=nvme boot/bench/run.sh` (`nvme` may join other parallel timings in the list) runs
`parallel_nvme` (`boot/dom0-bench/src/nvme/parallel.rs`) on the parallel call timing's workers: worker 0 is dom0 on CPU 0,
worker k the client of pair k on CPU k. dom0 resets the controller, sends Set Features Number of Queues, and creates
I/O queue pair k + 1 for worker k with its own rings (min(1024, CAP.MQES + 1) entries), 32 data buffers and doorbells,
polled; only dom0's first thread uses the admin queue, before any worker runs and after all are done, so neither
needs a lock. Workers = min(CPUs, the queue pairs the controller allocates, 24): at most 24 because the workers are
the call pairs. Worker k reads or writes 4 KiB sequentially within its own 1/n of namespace 1 (the LBA size comes
from Identify Namespace); batch b = at most b requests in flight on its queue, refilled each round with one doorbell
write. Per op and batch (read 1, read 32, write 1, write 32), each worker runs alone for `VERIFLAT_NVME_PARALLEL_MS`
(default 1000) while the others spin, then all at once until one shared deadline; then the controller is disabled.

| line | what it reports |
| --- | --- |
| `parallel_nvme cpu=k op=<read\|write> batch=b alone=A conc=C ratio=R` | IOPS of worker k alone and with all workers at once; `ratio` = conc / alone |
| `parallel_nvme summary op=.. batch=b n=.. total_conc=T sum_alone=.. median_alone=M scaling=S ...` | `total_conc`: every completion of the concurrent phase over its span from the first worker's start to the last one's end; `scaling` = T / M; the ratios' min and median; the share of the span in which all workers ran (`overlap`) |

It drives the NVMe function picked as above (`VERIFLAT_NVME_BDF`, required on bare metal) and leaves other NVMe
functions alone, so with two SSDs it measures one of them; without a picked function it logs `parallel_nvme skipped`.
Under QEMU every doorbell is a VM exit into QEMU's one NVMe device thread, so the total stays near the
single-queue rate whatever the CPU count (2026-11-12, KVM, SMP 1/2/4/8: total_conc at read batch 32 74K / 58K /
74K / 58K IOPS, each worker's ratio about 1/n); these runs show only that the queues work. Like the other NVMe
benchmark, it overwrites the SSD. For a real machine build the no-timer image, `cd boot && VERIFLAT_PARALLEL=nvme
cargo +1.99.1 build --profile release -p aloader -p kernel -p dom0-bench --features kernel/no-timer,dom0-bench/no-timer`, and
boot it as below; `maxcpus=<n>` on the `multiboot2` line gives the IOPS at n cores, one boot per count.

### Cross-process parallel NVMe benchmark (driver and application in two processes)

`NO_TIMER=1 SMP=n VERIFLAT_PARALLEL=nvme,nvme_xproc boot/bench/run.sh` runs `parallel_nvme` and then `parallel_nvme_xproc`
(`boot/dom0-bench/src/nvme/parallel_xproc.rs`), the same workload with the driver and the application in two processes
that pass work by IPC, one pair per CPU; one boot gives per core count the linked-in multi-queue IOPS and the
cross-process IOPS, and their ratio is the cost of the IPC. `nvme_xproc` alone runs only the second.

- Driver process: a child of dom0 sharing dom0's image, with its own IOMMU table. Its first thread takes the NVMe
  function (`send_pci`) from dom0, maps BAR0 itself, attaches the function to its IOMMU table, resets the
  controller, sends Set Features Number of Queues and creates I/O queue pair k + 1 (rings in its own heap) for each
  worker k, then creates driver thread k, which owns that queue pair alone; the first thread keeps only the admin
  queue and, after the last run, disables the controller.
- Application: dom0, as in `parallel_nvme`: worker 0 is dom0's first thread on CPU 0, worker k the client of parallel
  call pair k on CPU k.
- Endpoints: dom0 creates one handoff endpoint before the call pairs start and gives it to each pair client over the
  pair's endpoint while the client is still on CPU 0, before the pair's server exists (a client created later could
  receive nothing: its server occupies the pair's endpoint); the driver process holds it as its first endpoint. Worker
  k creates its own endpoint and sends it to driver thread k over the handoff endpoint, one pair at a time; from then
  on the pair uses only that endpoint. A `call` runs the waiting driver thread on the caller's CPU, so driver thread k
  runs on CPU k without any placement.
- Buffers, shared as the `ipc` configuration shares its ring: worker k maps a region of 33 pages in dom0 (a control
  page, then 32 4 KiB data buffers, at `0xdc_0000_0000 + k * 2 MiB`) and shares it with `send_pages`; driver thread k
  receives it at the same address and maps it into the driver process's IOMMU table at IOVA = VA, so the controller
  reads and writes the application's buffers directly.
- One IPC round trip per round: worker k writes up to b - (requests in flight) new requests (LBA, buffer, op) into its
  control page and calls driver thread k with their count (`call_usize`); the driver thread submits them with one
  doorbell write, reaps every posted completion, waiting for at least one while any request is in flight, writes
  their buffer numbers into the control page and answers with their count (`reply_and_receive_usize`). At batch 1 that
  is one round trip per request; at batch 32 one round trip per group of completions.

Workers = min(CPUs, the queue pairs the controller allocates, 24), as for `parallel_nvme`; LBA ranges, ops, batches,
phases, `VERIFLAT_NVME_PARALLEL_MS` and the drive selection are the same. The lines are those of `parallel_nvme`
with the prefix `parallel_nvme_xproc` (`total_conc` is the total IOPS of the concurrent phase), plus per run
`parallel_nvme_xproc calls op=.. batch=b n=.. calls=C per_call=P`: the round trips of the concurrent phase and its
completions per round trip. Afterwards the driver process is killed, which leaves the function unowned, dom0 claims
it again and unmaps the regions. Without the NVMe function it logs `parallel_nvme_xproc skipped`; an LBA size above 4 KiB skips it
too.

Under KVM (2026-11-12, emulated NVMe, so the device is the bottleneck and the numbers show only that it works),
`total_conc` IOPS of `parallel_nvme` / `parallel_nvme_xproc` at read batch 32 and read batch 1:

| SMP | `parallel_nvme` read b=32 | `parallel_nvme_xproc` read b=32 | `parallel_nvme` read b=1 | `parallel_nvme_xproc` read b=1 |
| --- | --- | --- | --- | --- |
| 1 | 55.2K | 38.2K | 7.7K | 7.5K |
| 2 | 69.9K | 73.2K | 17.0K | 18.9K |
| 4 | 63.4K | 54.1K | 15.2K | 18.4K |
| 8 | 39.6K | 58.5K | 15.2K | 9.0K |

The two benchmarks swap places from run to run: QEMU's single device thread sets both rates. At batch 32 a round trip
answered 15 to 26 completions. The SMP 4 run also ran `call` before them (the clients then hold the handoff endpoint
while the call timing runs), and its call timings passed unchanged.

For the real machine build the no-timer image with both, `cd boot && VERIFLAT_PARALLEL=nvme,nvme_xproc cargo +1.99.1
build --profile release -p aloader -p kernel -p dom0-bench --features kernel/no-timer,dom0-bench/no-timer`, and boot it with
`maxcpus=<n>` as for `parallel_nvme`.

### Real hardware

Not yet tried on a real machine. The target is a CloudLab d430 (2x Xeon E5-2630 v3, Haswell: no RDPID, no
CPUID leaf 16H; the NVMe SSD sits behind a PCIe root port). The machine needs VT-d on. An assigned BAR0 stays where
the firmware put it, below or above 4 GiB, and dom0 maps it with the BAR syscalls; the loader moves an unassigned BAR0
only on bus 0, and on any other bus it skips an NVMe, Ethernet or `edu` function whose BAR0 is unassigned with a
warning that names the function, so that such a device stays out of dom0 but does not stop the boot.

The GRUB `multiboot2` path below has been booted under QEMU (KVM, q35, the devices of `boot/bench/run.sh`) and passes
the NVMe benchmark and the dom0 tests: from a `grub-mkrescue` ISO with GRUB 2.12 on SeaBIOS, with `serial=com2`
too (the loader's and the kernel's output then arrive on the second serial port; only the loader's first lines
and one kernel line printed before the kernel reads its command line stay on COM1), and from a standalone GRUB 2.14
x86_64-efi image on OVMF, where the loader takes the RSDP from GRUB's ACPI tags since UEFI has none in the BIOS
area. Untried on hardware: the server's firmware memory map, ACPI tables, VT-d units and serial ports, GRUB as
installed on the server's disk, and the real SSD.

1. Build with 30 s runs: `cd boot && VERIFLAT_NVME_SECS=30 cargo +1.99.1 build --profile release -p aloader -p kernel -p dom0-bench`.
   The E5-2630 v3 has no leaf 16H, so outside a hypervisor dom0 takes the TSC rate from the brand string's
   "@ 2.40GHz"; `VERIFLAT_TSC_MHZ=<MHz>` in the same build overrides it. Concatenate the kernel and dom0 as
   `boot/bench/run.sh` does, `cat kernel dom0-bench > veriflat-jumbo` in `boot/target/x86_64-unknown-none/release/`, and copy
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
from `-append`, e.g. `NO_TIMER=1 SMP=8 boot/bench/run.sh -append maxcpus=2`.

The boot option `turbo=off` makes every CPU that comes up set IA32_MISC_ENABLE bit 38 (Turbo Mode Disable) when
CPUID.06H:EAX bit 1 reports turbo, and read it back; on an Intel CPU outside a hypervisor without that CPUID bit it
only reads the MSR, to tell firmware-disabled turbo from none. The kernel logs "turbo=off: IA32_MISC_ENABLE bit 38
set on k of n CPUs (s set here, a already set)" and warns for each CPU without it; under KVM nothing is written and
every CPU gets that warning. Independently of the option, when CPUID.06H:ECX bit 0 reports APERF/MPERF, CPU 0 reads
them before it enters dom0 and again where the RAM log is finalised (exit, panic, fatal exception, `reset_after`),
and logs "effective frequency: CPU 0 <f> MHz = TSC <t> MHz (from <source>) x APERF/MPERF <ratio> (<dA> / <dM>),
unhalted <p>% of <c> TSC cycles", the mean frequency while CPU 0 was not halted (`boot/kernel/src/power.rs`); without
the CPUID bit, as under KVM, it logs once that the frequency is not measured.

The local APIC runs in the mode the firmware hands over: xAPIC as before, or x2APIC, which the kernel then keeps on
every CPU (`boot/kernel/src/interrupt/lapic.rs`); the boot option `x2apic=on` switches it from xAPIC to x2APIC when
CPUID.01H:ECX bit 21 reports x2APIC (`x2apic=off`, the default, keeps the firmware's mode), e.g. `boot/bench/run.sh -append
x2apic=on` under KVM, whose `-cpu host` reports it. The kernel logs "x2apic=on: switched the local APIC from xAPIC to
x2APIC mode" when it switches and always "local APIC mode: <xAPIC|x2APIC>, boot CPU APIC ID <id>". The loader takes
processors from MADT local APIC (type 0) and local x2APIC (type 9) entries and logs "MADT: <a> local APIC and <b>
local x2APIC entries, <n> enabled processors taken"; an APIC ID above 254 is refused with a warning and that processor
stays down. The loader accepts up to 16 VT-d remapping units (`MAX_IOMMU_UNITS`) and panics on more.

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
throughput scaling with cores on a CloudLab c6620. It was written against the Linux `ice` headers (read as a reference)
and a software device model, and has run on an E810-C (firmware 7.10.1, 100G) on c6620 er042 since 2026-11-14, from
Linux user space and from dom0 (bare-metal scripts and results: the artifact repository's `baremetal/nic-*`).

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
- `boot/dom0-bench/src/ice_bench.rs`: the dom0 front end, built with feature `ice-bench` (`ICE_BENCH=1 boot/bench/run.sh`). It runs
  first and alone, finds the E810 with `sys_pci_info` (`VERIFLAT_ICE_BDF=bb:dd.f`, else the first E810-C, else the
  first E810), claims it, maps BAR0 at `0xd0_0000_0000 + base` (`boot/dom0-bench/src/bar.rs`; 2M pages for the
  E810's 2M-aligned BAR0), attaches it with `pci_attach_dma`, drives BAR0 there and takes DMA memory from
  the heap (IOVA = VA). Worker k runs on CPU k (placed as the parallel call timing places its clients) and owns
  queue pair k. The device comes up once with one queue pair per worker; then one round runs per frame size, mode and
  queue count. Build-time settings: `VERIFLAT_ICE_SECS` (5, per round), the comma-separated lists
  `VERIFLAT_ICE_QUEUES` (one per CPU), `VERIFLAT_ICE_FRAME` (64, with CRC) and `VERIFLAT_ICE_MODE` (`tx`, `rx`,
  `both`, default `both`; `rx` adds a sender on the last CPU that sends the measured queues' frames in turn, so it needs
  a CPU besides the measured queues), `VERIFLAT_ICE_POOL` (64, copies of each queue's frame), `VERIFLAT_ICE_DST` or
  `VERIFLAT_ICE_PEER` (+ `VERIFLAT_ICE_PEER_QUEUES`), `VERIFLAT_ICE_STEER` (`mac`, `promisc`), `VERIFLAT_ICE_LINK_SECS`
  (15). Mode `fwd` (last in the list, it leaves the Tx rings off their batch alignment) forwards instead
  (`ice::bench::run_forwarder`, the per-packet work of Atmosphere's maglev benchmark in `ice::maglev`: flow hash, flow
  cache, 65537-entry lookup table over 3 backends, MAC rewrite, zero-copy transmit) to `VERIFLAT_ICE_FWD_DST`: worker k
  of n forwards what queues k, k + n, .. receive, so a generator that spreads its frames over all steering MACs loads
  every worker count fully; the extra line is `ice fwd: <n> workers, <pps> pps forwarded, <c> TSC cycles per
  forwarded frame per worker`. `ice-linux --mode fwd --fwd-workers n --fwd-dst MAC` runs the same, and
  `ice-linux --mode tx --gen-peer MAC --pool 1024` is the generator (a flow per frame copy, spread over the peer's
  28 steering MACs). Without an E810 it logs `ice bench skipped: no E810 function recorded`; the default dom0 test logs the same, or
  the E810 functions the loader recorded.
- `boot/dom0-bench/src/ice_xproc.rs`: the IPC variant, feature `ice-xproc` (`ICE_XPROC=1 boot/bench/run.sh`, skipped likewise
  without an E810). Application thread k (dom0, CPU k) hands up to 1 or 32 frames per batch to the driver's queue pair
  k and reads back what that queue received, through `ice::xfer` (a mailbox page and Tx slots per pair, Rx buffers
  handed out in place and re-armed at the next request, zero copy both ways; a Tx write-back once per 32 descriptors
  and Rx tail writes only when they hand the device more descriptors, since a write-back per frame held the whole port
  to about 11.5 Mpps): first `ice_linked`, the driver called
  directly, then `ice_xproc`, the driver in a child process (`new_process_with_iommu_and_endpoint`) with one thread per
  pair, one `call` + `reply_and_receive` round trip per batch on the pair's endpoint, CPU k switching straight between
  the two threads. The driver process gets the function (`send_pci`; dom0 unmapped its own BAR0 mapping after
  `ice_linked`), maps BAR0 and attaches the function itself, and gets the shared region (`send_pages`, the same pages mapped in both; it maps the region into its IOMMU table at IOVA = VA) and
  the endpoints (`send_endpoint`). At most 31 cross-process pairs (endpoint descriptors per thread).
  `VERIFLAT_ICE_QUEUES` lists pair counts c at which the first c pairs also run at once before all do
  (`ice_linked|ice_xproc conc batch=b n=c total_conc=.. rx_total_conc=..`). Lines:
  `ice_linked|ice_xproc cpu=k batch=b alone=<pps> conc=<pps> ratio=<alone/conc> ..`, a summary per batch size with
  the total pps, and `ice_ipc_cost` comparing both. `ICE_MOCK=1` (feature `ice-mock`) runs both on the device model
  (`ice::mock`, each queue's frames looped back to itself and checked by sequence number): numbers of the IPC and the
  model, not a NIC. The E810 benchmarks run on a kernel without the timer (`run.sh` builds it so), since a tick on
  CPU 0 could let a CPU coming online pull dom0's first thread instead of thread k.
- `boot/dom0-bench/src/ice_chan.rs` with `boot/ice/src/chan.rs`: the shapes of the Atmosphere paper's NIC figure over one
  application/driver exchange (`ice::chan`: per pair two single-producer single-consumer rings of frame entries and a
  few counters in memory both processes map, zero copy both ways), which the Atmosphere port runs unchanged, feature
  `ice-chan` (`ice-chan-mock` on the device model; kernel without the timer). `VERIFLAT_ICE_SHAPE` picks
  `linked` (driver process thread k on CPU k + 1 runs both sides of pair k, no IPC), `ipc` (application thread k in
  dom0 on CPU k, one `call` per batch to driver thread k on the same CPU) or `ring` (application thread k on CPU k,
  driver thread k polling on CPU P + k, P = half the CPUs, no IPC). Modes (`VERIFLAT_ICE_MODE`, default
  `tx,rx,fwd,maglev`): `tx` (frames with sequence numbers from Tx slots), `rx` (received frames read in place and
  released), `fwd` (each received frame's MACs rewritten and sent back out from its Rx buffer, the work of
  Atmosphere's `run_fwd_udptest`) and `maglev` (`ice::maglev` per frame, then the rewrite). `VERIFLAT_ICE_BATCH`
  (`1,32`), `VERIFLAT_ICE_QUEUES` (pair counts), `VERIFLAT_ICE_WINDOW_MS` (1000), `VERIFLAT_ICE_FWD_DST` (needed for
  fwd and maglev). The device has one queue pair per CPU; pair k of c polls Rx queues k, k + c, ... Line per phase:
  `ice_linked|ice_ring|ice_ipc mode=m batch=b n=c total=<pps> min= max= overlap= pairs=<pps>,..` (frames the
  application side moved: pushed for transmission, received, forwarded). Bare-metal runs:
  `VeriFlat-artifact/baremetal/nic-chan.sh`.
  Payload paths (2026-11-25; feature `dom0-bench/payload-path`, `PAYLOAD_PATH=1` for run.sh, src/ice_chan_payload.rs
  and boot/ice/src/chan_payload.rs; the default build has the zero-copy channel only, with the code and layout of
  c25c2277, and refuses at build time any of the settings below other than path zero, touch off, frames up to 1518):
  `VERIFLAT_ICE_PATH` `zero` (default), `copy` (private application buffers, one copy into
  a shared Tx slot and one out of a shared Rx buffer per frame) or `map` (the Rx buffers' pages move between the
  processes with `send_pages` + `unmap_4k` through couriers, src/courier.rs, and leave / re-enter the driver's IOMMU
  table; at most 8 pairs, shapes ipc and ring; mode tx stays zero copy; `VERIFLAT_ICE_MAP_IOMMU=0` keeps the pages in
  the IOMMU table); `VERIFLAT_ICE_TOUCH`, a list of `off`, `read`, `write`, each run over every batch and pair count
  (the application reads or writes every payload byte); `VERIFLAT_ICE_FRAME` 64..9000 (above 1518 the port is set to
  9728-byte frames and buffers hold a whole frame). The line gains `path= touch= frame=`; path map adds
  `ice_map_counts` (runs and pages given per side). `ICE_CHAN_MOCK=1 boot/bench/run.sh` runs it on the device model.
- `boot/dom0-bench/src/handoff.rs`, `VERIFLAT_PARALLEL=iommu,handoff` or `flushcpus` (no-timer build with feature
  `dom0-bench/payload-path`, run first and alone): `iommu_prim` lines (`iommu_map_4k` / `iommu_unmap_4k` of 1, 8, 32, 64 pages without and with a device
  attached to the table), `handoff` lines (payload hand-off of 4 KiB to 2 MiB between dom0 and a child process, same
  core and two cores: local, pool, copy, copy2, map; cycles per round), `flushcpus` lines (`unmap_4k` of 1 and 16 pages
  while dom0 threads spin on 1, 2, 4, 8, 16, 28 CPUs).

Each queue sends one fixed UDP frame from its steering MAC (so that a reflector which swaps the MACs returns it to
the same queue), one descriptor per frame cycling over the frame's 64 copies (`VERIFLAT_ICE_POOL`, `--pool`; one
buffer sent over and over reaches only 12 to 26 Mpps per queue in dom0), report status on the last of each
32-descriptor batch, and counts what its Rx queue receives (buffers re-armed in place). A queue that only receives
waits 4000 TSC cycles after a poll that found fewer than 32 frames (`RX_HOLDOFF_CYCLES` in `ice/src/bench.rs`):
polling the descriptor the NIC writes back without a pause slows the whole port. The result lines are
`ice queue <q> cpu <q>: tx <pps> pps, rx <pps> pps, rx errors <n>`, `ice total: mode <m> queues <n> frame <s>: tx ..
pps, rx .. pps over <n> queues; line rate of <s>-byte frames at <Mb/s> is <pps> pps`, `ice sender cpu <k>: ..` (mode
`rx`), and `ice port: ..` with the port counters over the round (`GLPRT_*`, flow control, and the VSI's and Rx packet
buffer's drops); the Linux program prints the same without the `ice` prefix. 64-byte transmit tops out at 117.2 Mpps
on this E810 from Linux and dom0 alike (not flow control, ring or batch size, or PCIe; 128-byte frames reach line
rate), so 64-byte rates at that value are the NIC's, not the kernel's.

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
through the Tx queues, the steering rules and the Rx queues); the bare-metal build of `ice` and `dom0-bench` with and without
`ice-bench`; the Linux program's build and argument handling; `boot/bench/run.sh` and `ICE_BENCH=1 boot/bench/run.sh` under KVM
with SMP 4, both passing with the skip line. The device model encodes the same reading of the specification as the
driver, so it finds plumbing errors, not misreadings.

`ICE_MOCK=1 boot/bench/run.sh` under KVM (2026-11-12, i9-13900HX under WSL2, 100 ms windows, 64-byte frames), total pps of
all pairs at once and the median extra TSC cycles per batch of `ice_xproc` over `ice_linked` alone; the IPC and the
device model, not a NIC:

| SMP | batch 1 linked | batch 1 xproc | batch 32 linked | batch 32 xproc | IPC cycles per batch (1 / 32) |
| --- | --- | --- | --- | --- | --- |
| 1 | 19.2M | 3.01M | 28.3M | 19.1M | 669 / 775 |
| 2 | 38.4M | 5.33M | 55.0M | 42.1M | 687 / 787 |
| 4 | 70.6M | 11.6M | 103.5M | 79.4M | 712 / 924 |
| 8 | 122.2M | 20.5M | 170.1M | 143.5M | 692 / 876 |

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
| dom0: worker placement on CPUs coming online, heap DMA at IOVA = VA above 4 GiB, BAR0 as uncached 2M IO leaves of `map_pci_bar_2m` | VeriFlat | untested with any NIC |
| `ice_xproc`: function and shared region handed to the driver process, which maps BAR0 itself, its IOMMU table, per-frame report status | VeriFlat | run on the model only |

Kernel and loader gaps:

- BAR0 placement: the E810's BAR0 is a 64-bit prefetchable BAR (32 MiB on the E810-C: Atmosphere's c6620 run found
  it at 0xfa000000, size 0x2000000). The loader now reports every assigned memory BAR, above 4 GiB too, and maps none;
  dom0 claims the function and maps BAR0 as 16 uncached 2M IO pages (`map_pci_bar_2m`, `boot/dom0-bench/src/bar.rs`),
  so above-4G decoding may stay on. The bare-metal runs of 2026-11-14 predate this and used the loader's BAR0 mapping.
- No MSI-X or interrupts are needed (polling); BAR3 (MSI-X table) stays unmapped.
- At most 16 recorded functions (`MAX_PCI_DEVICES`); a c6620 has 2 + 2 E810 ports plus NVMe and other NICs.
- 28 CPUs at most (`NUM_CPUS`): the loader takes the first 28 processors of the ACPI MADT list; boot with `maxcpus=` on a machine with more logical processors.

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
   --profile release -p aloader -p kernel -p dom0-bench --features kernel/no-timer,dom0-bench/ice-bench` (for the IPC variant
   `--features kernel/no-timer,dom0-bench/ice-xproc`, with `VERIFLAT_ICE_WINDOW_MS=1000`), then concatenate kernel and dom0-bench into
   the jumbo image and boot it from GRUB as in the NVMe section above (`maxcpus=<n>` for n queue pairs, and the RAM
   log for unattended runs). The peer runs the Linux program (`--mode rx --peer <this port's MAC>` or `--mode both`).
3. Read the `ice queue`, `ice total` and `ice port` lines; `ice bench passed` ends the run (`ice xproc bench passed`
   after the `ice_linked`, `ice_xproc` and `ice_ipc_cost` lines for the IPC variant).
