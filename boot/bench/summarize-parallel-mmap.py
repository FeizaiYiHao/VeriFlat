"""Summarizes the parallel mmap timing in run-parallel-call.sh's extracted.txt of each results directory,
over the runs that its status.txt lists as passed (QEMU status 1). Per mode and SMP, across those runs:
the median of each run's median alone and concurrent TSC cycles per round across CPUs and of its median
ratio, the overlap range and how many runs reached 0.50, and the concurrent cycles over the median alone
cycles of the SMP=1 runs of the same mode (`vs smp1`), which leaves out what the other CPUs cost a worker
alone (in the same-process modes, its unmap flushes their TLBs). Runs whose overlap stayed below 0.50
are left out of the medians unless no run reached it. Also the single-CPU mmap timers per SMP.
Usage: python3 -I summarize-parallel-mmap.py <results_dir>..."""
import collections, os, re, statistics, sys

ansi = re.compile(r'\x1b\[[0-9;]*[A-Za-z]')
run_re = re.compile(r'smp=(\d+) run=(\d+):')
cpu_re = re.compile(r'(parallel_mmap\w*) cpu=(\d+) alone=(\d+) conc=(\d+) ratio=([\d.]+)')
sum_re = re.compile(r'(parallel_mmap\w*) summary n=(\d+) min_ratio=([\d.]+) max_ratio=([\d.]+) median_ratio=([\d.]+) overlap=([\d.]+)'
                    r' \(rounds per pair: alone (\d+)\.\.(\d+), conc (\d+)\.\.(\d+)\)')
short_re = re.compile(r'(parallel_mmap\w*) quota: region (\d+) pages per worker, (\d+) early region unmaps')
timer_res = [
    (re.compile(r'mmap\+unmap 4K: (\d+) TSC cycles per page'), lambda m: 'mmap+unmap 4K per page (64 per call)'),
    (re.compile(r'mmap 4K: (\d+) TSC cycles per page, (\d+) pages per call'), lambda m: f'mmap 4K per page ({m[2]} per call)'),
]
MODES = ['parallel_mmap_same', 'parallel_mmap_xproc', 'parallel_mmap_only_same', 'parallel_mmap_only_xproc', 'parallel_mmap_cached_xproc']
MIN_OVERLAP = 0.50


def med(values):
    return statistics.median(values) if values else float('nan')


def summarize(results):
    print(f"#### {results}")
    passed = set()
    for line in open(os.path.join(results, 'status.txt')):
        m = re.match(r'smp=(\d+) run=(\d+) status=(\d+)', line)
        if m and m[3] == '1':
            passed.add((int(m[1]), int(m[2])))
        elif m:
            print(f"FAILED: smp={m[1]} run={m[2]} status={m[3]} (excluded)")
    cpus = collections.defaultdict(dict)  # (mode, smp, run) -> cpu -> (alone, conc)
    sums = collections.defaultdict(dict)  # (mode, smp) -> run -> summary
    shorts = collections.defaultdict(int)  # (mode, smp) -> early region unmaps over all runs
    timers = collections.defaultdict(lambda: collections.defaultdict(list))  # smp -> name -> values
    for line in open(os.path.join(results, 'extracted.txt'), errors='replace'):
        line = ansi.sub('', line)
        m = run_re.match(line)
        if not m or (int(m[1]), int(m[2])) not in passed:
            continue
        smp, run = int(m[1]), int(m[2])
        if m := cpu_re.search(line):
            cpus[(m[1], smp, run)][int(m[2])] = (int(m[3]), int(m[4]))
        elif m := sum_re.search(line):
            sums[(m[1], smp)][run] = dict(n=int(m[2]), mn=float(m[3]), mx=float(m[4]), ratio=float(m[5]), ov=float(m[6]),
                                          alone_rounds=(int(m[7]), int(m[8])), conc_rounds=(int(m[9]), int(m[10])))
        elif m := short_re.search(line):
            shorts[(m[1], smp)] += int(m[3])
        else:
            for regex, name in timer_res:
                if m := regex.search(line):
                    timers[smp][name(m)].append(int(m[1]))
                    break
    smps = sorted({smp for (_, smp) in sums})
    for smp in smps:
        if timers[smp]:
            print(f"== SMP={smp} single-CPU timers: " + "; ".join(f"{name} median {med(v):g} ({min(v)}..{max(v)})" for name, v in timers[smp].items()))
    base = {}
    for mode in MODES + sorted({mode for (mode, _) in sums} - set(MODES)):
        if not any((mode, smp) in sums for smp in smps):
            continue
        print(f"== {mode}")
        for smp in smps:
            runs = sums.get((mode, smp))
            if not runs:
                continue
            good = [r for r in runs if runs[r]['ov'] >= MIN_OVERLAP]
            used = good or list(runs)
            alone = [med([a for a, _ in cpus[(mode, smp, r)].values()]) for r in used]
            conc = [med([c for _, c in cpus[(mode, smp, r)].values()]) for r in used]
            if smp == 1:
                base[mode] = med(alone)
            vs = f", vs smp1 {med(conc) / base[mode]:.2f}" if mode in base else ""
            ovs = [runs[r]['ov'] for r in sorted(runs)]
            rounds = [runs[r]['conc_rounds'] for r in used]
            note = "" if good else " (no run reached the overlap; medians over all runs)"
            print(f"SMP={smp} n={runs[used[0]]['n']}: alone {med(alone):.0f} conc {med(conc):.0f} ratio {med([runs[r]['ratio'] for r in used]):.2f}{vs}; "
                  f"overlap {min(ovs):.2f}..{max(ovs):.2f}, {len(good)}/{len(runs)} runs >= {MIN_OVERLAP:.2f}{note}; "
                  f"conc rounds per worker {min(lo for lo, _ in rounds)}..{max(hi for _, hi in rounds)}"
                  + (f"; {shorts[(mode, smp)]} early region unmaps" if shorts[(mode, smp)] else ""))


for results in sys.argv[1:]:
    summarize(results)
