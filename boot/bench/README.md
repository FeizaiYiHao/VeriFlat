# dom0 timing benchmarks

Drivers for the TSC timings dom0 prints under KVM. Results and images go to `boot/bench/out/`
(gitignored). All numbers are TSC cycles.

## Build modes

- `boot/run.sh`: the full dom0 test with the LAPIC timer. It prints the null syscall, mmap, IPC,
  intra-process call, and new_thread timers on the way.
- `NO_TIMER=1 SMP=n boot/run.sh`: kernel and dom0 with feature `no-timer`. dom0 runs only the timers
  (adding the parallel call and cross-process call timers) and exits. Use this mode for measurements.

QEMU exits with status 1 when dom0 passed (isa-debug-exit maps code 0 to 1).

## Scripts

- `build-parallel-call-image.sh [out_dir]`: builds the no-timer image as `NO_TIMER=1 boot/run.sh`
  does and stores `aloader`, `jumbo` (kernel ELF then dom0 ELF), and `built-from.txt` (commit, dirty
  `src/` and `boot/` files, hashes) in `out_dir`, default `out/image`. `WORKTREE=<checkout>` builds
  another checkout, such as a `git worktree add` of a baseline commit.
- `run-parallel-call.sh <runs> <smp>...`: boots the stored image `runs` times at each SMP count with
  `taskset -c 0-31`, KVM, `-cpu host`, `q35,kernel_irqchip=split`, `-m 6144 -mem-prealloc`, and
  isa-debug-exit, each under a 300 s `timeout`. Per run it appends the status to `status.txt` and the
  timer lines to `extracted.txt` in `OUT` (default `out/results`) and deletes the raw log of a passing
  run. `IMAGE` picks the image; `B_IMAGE` (and `B_OUT`, default `out/results-b`) turns on A/B mode;
  `FIRST_RUN` numbers further runs into the same directories.
- `summarize-parallel-call.py <results_dir>...`: over the passing runs of each directory, per SMP the
  median, min, and max of every timer, and the parallel call table of the median run with the ranges
  across runs. Run it with `python3 -I`.

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

A ratio near 1.00 means the pairs do not slow each other down through the kernel.

## Interleaved A/B protocol

1. Build both images: `WORKTREE=<baseline checkout> boot/bench/build-parallel-call-image.sh boot/bench/out/image-a`
   and `boot/bench/build-parallel-call-image.sh boot/bench/out/image-b`.
2. Run them interleaved, 5 runs each:
   `IMAGE=boot/bench/out/image-a OUT=boot/bench/out/results-a B_IMAGE=boot/bench/out/image-b B_OUT=boot/bench/out/results-b boot/bench/run-parallel-call.sh 5 4`.
   Every run boots A, then B, so host drift hits both alike.
3. Every run must exit with status 1. Compare the medians over the 5 runs:
   `python3 -I boot/bench/summarize-parallel-call.py boot/bench/out/results-a boot/bench/out/results-b`.
