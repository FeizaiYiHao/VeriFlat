"""Summarizes run-parallel-call.sh's extracted.txt of each results directory, over the runs that its
status.txt lists as passed (QEMU status 1): per SMP the single-thread timers (median, min, max across
runs, in TSC cycles), the per-CPU parallel call table of the median run (by median ratio), and the
parallel call ranges across CPUs and runs. In A/B mode pass both directories.
Usage: python3 -I summarize-parallel-call.py <results_dir>..."""
import collections, os, re, statistics, sys

ansi = re.compile(r'\x1b\[[0-9;]*[A-Za-z]')
run_re = re.compile(r'smp=(\d+) run=(\d+):')
cpu_re = re.compile(r'parallel_call cpu=(\d+) alone=(\d+) conc=(\d+) ratio=([\d.]+)')
sum_re = re.compile(r'parallel_call summary n=(\d+) min_ratio=([\d.]+) max_ratio=([\d.]+) median_ratio=([\d.]+) overlap=([\d.]+)')
# Each timer line of dom0 and the values it reports, in TSC cycles.
timers = [
    (re.compile(r'null syscall: (\d+) TSC cycles returning through sysretq, (\d+) through iretq'), ['null syscall sysretq', 'null syscall iretq']),
    (re.compile(r'mmap\+unmap 4K: (\d+) TSC cycles per page'), ['mmap+unmap 4K per page']),
    (re.compile(r'mmap 4K: (\d+) TSC cycles per page, (\d+) pages per call'), None),
    (re.compile(r'IPC round trip: (\d+) TSC'), ['IPC round trip']),
    (re.compile(r'call round trip: (\d+) TSC'), ['call round trip']),
    (re.compile(r'call round trip cross process: (\d+) TSC'), ['call round trip cross process']),
    (re.compile(r'new_thread: best (\d+) TSC cycles, mean (\d+)'), ['new_thread best', 'new_thread mean']),
]


def summarize(results):
    print(f"#### {results}")
    passed = set()
    for line in open(os.path.join(results, 'status.txt')):
        m = re.match(r'smp=(\d+) run=(\d+) status=(\d+)', line)
        if m and m[3] == '1':
            passed.add((int(m[1]), int(m[2])))
        elif m:
            print(f"FAILED: smp={m[1]} run={m[2]} status={m[3]} (excluded)")
    cpus = collections.defaultdict(dict); sums = collections.defaultdict(dict)
    values = collections.defaultdict(lambda: collections.defaultdict(dict))
    for line in open(os.path.join(results, 'extracted.txt'), errors='replace'):
        line = ansi.sub('', line)
        m = run_re.match(line)
        if not m or (int(m[1]), int(m[2])) not in passed:
            continue
        smp, run = int(m[1]), int(m[2])
        if m := cpu_re.search(line):
            cpus[(smp, run)][int(m[1])] = (int(m[2]), int(m[3]), m[4])
        elif m := sum_re.search(line):
            sums[smp][run] = dict(n=int(m[1]), mn=float(m[2]), mx=float(m[3]), med=float(m[4]), ov=float(m[5]))
        else:
            for regex, names in timers:
                if m := regex.search(line):
                    names = names or [f"mmap 4K per page ({m[2]} per call)"]
                    for name, value in zip(names, m.groups()):
                        values[smp][name][run] = int(value)
                    break
    for smp in sorted(set(sums) | set(values)):
        print(f"== SMP={smp}")
        for name, per_run in values[smp].items():
            runs = [per_run[r] for r in sorted(per_run)]
            print(f"{name}: median {statistics.median(runs):g} min {min(runs)} max {max(runs)} (runs: {' '.join(map(str, runs))})")
        runs = sums[smp]
        if not runs:
            continue
        order = sorted(runs, key=lambda r: (runs[r]['med'], r))
        mid = order[(len(order) - 1) // 2]
        print(f"parallel_call: {len(runs)} runs, median run = run {mid} (n={runs[mid]['n']})")
        print("cpu  alone  conc  ratio")
        for cpu, (a, c, r) in sorted(cpus[(smp, mid)].items()):
            print(f"{cpu:3d} {a:6d} {c:5d}  {r}")
        print("per run: " + "; ".join(f"run {r}: min {runs[r]['mn']:.2f} med {runs[r]['med']:.2f} max {runs[r]['mx']:.2f} overlap {runs[r]['ov']:.2f}" for r in sorted(runs)))
        print(f"across runs: min ratio {min(v['mn'] for v in runs.values()):.2f}, max ratio {max(v['mx'] for v in runs.values()):.2f}, "
              f"median ratio {min(v['med'] for v in runs.values()):.2f}..{max(v['med'] for v in runs.values()):.2f}, "
              f"overlap {min(v['ov'] for v in runs.values()):.2f}..{max(v['ov'] for v in runs.values()):.2f}")


for results in sys.argv[1:]:
    summarize(results)
