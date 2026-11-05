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
  128-page working set right after it).
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
  `taskset -c 0-31`, KVM, `-cpu host`, `q35,kernel_irqchip=split`, `-m 6144 -mem-prealloc`, and
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

A ratio near 1.00 means the pairs do not slow each other down through the kernel.

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

## Interleaved A/B protocol

1. Build both images: `WORKTREE=<baseline checkout> boot/bench/build-parallel-call-image.sh boot/bench/out/image-a`
   and `boot/bench/build-parallel-call-image.sh boot/bench/out/image-b`.
2. Run them interleaved, 5 runs each:
   `IMAGE=boot/bench/out/image-a OUT=boot/bench/out/results-a B_IMAGE=boot/bench/out/image-b B_OUT=boot/bench/out/results-b boot/bench/run-parallel-call.sh 5 4`.
   Every run boots A, then B, so host drift hits both alike.
3. Every run must exit with status 1. Compare the medians over the 5 runs:
   `python3 -I boot/bench/summarize-parallel-call.py boot/bench/out/results-a boot/bench/out/results-b`.
