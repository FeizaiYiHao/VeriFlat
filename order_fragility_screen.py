#!/usr/bin/env python3
"""Order-fragility screen for Verus proof functions (a diagnostic tool, not part of integration).

Usage:
  ./order_fragility_screen.py [--all-eof | --modules M [M ...] | --smt-dir DIR] [--functions all|eof]
                              [--jobs 8] [--threads 8] [--shuffles 8] [--rlimit 30000000] [--timeout 900]
                              [--work DIR] [--keep]

Logs the SMT queries of the given monolith modules (`--all-eof`: every module whose file defines a `*_eof*` or
`*_eol*` function) with `./verify.sh --log smt`, then replays every logged module file in one z3 process in its
original order and in N seeded orders that shuffle each contiguous run of top-level asserts (prelude and context
included). Each function query is cut at its first check-sat, so a retry query after a failure is never scored.
Prints, per function: result in every order, rlimit min-max and spread (max/min); flags any failure or spread > 3.
`--smt-dir` replays an existing log directory instead (for example one written by
`./verify-workspace.sh --package P -- --verify-only-module M --log smt --log-dir DIR`).
"""
import argparse, os, random, re, shutil, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.abspath(__file__))
Z3 = os.path.join(ROOT, "verus/source/z3")
EOF_FN = re.compile(r"\bfn\s+\w*_eo[fl]\w*")


def eof_modules():
    mods = []
    for d, _, files in os.walk(os.path.join(ROOT, "src")):
        for f in files:
            if not f.endswith(".rs"):
                continue
            p = os.path.join(d, f)
            with open(p, errors="replace") as fh:
                if not EOF_FN.search(fh.read()):
                    continue
            rel = os.path.relpath(p, os.path.join(ROOT, "src"))[:-3].split(os.sep)
            if rel[-1] == "mod":
                rel = rel[:-1]
            if len(rel) == 1 and (rel[0] == "lib" or rel[0].startswith("veriflat_")):
                continue
            mods.append("::".join(rel))
    return sorted(set(mods))


def log_modules(mods, out, threads):
    args = [os.path.join(ROOT, "verify.sh"), "--no-erasure-check", "--num-threads", str(threads), "--log", "smt", "--log-dir", out]
    for m in mods:
        args += ["--verify-only-module", m]
    r = subprocess.run(args, cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    errs = [l for l in r.stderr.splitlines() if l.startswith("error")]
    if errs:
        print("note: verify.sh reported:", *errs[:5], sep="\n  ", file=sys.stderr)


def parse(path):
    """Top-level items: ('fn', name, lines) | ('assert', None, lines) | ('other', None, lines)."""
    with open(path, errors="replace") as fh:
        lines = fh.read().split("\n")
    chunks, cur = [], []
    for l in lines:
        if l and not l[0].isspace() and l[0] != ")":
            if cur:
                chunks.append(cur)
            cur = [l]
        else:
            cur.append(l)
    if cur:
        chunks.append(cur)
    items, i, name, seen = [], 0, None, {}
    while i < len(chunks):
        c = chunks[i]
        if c[0].startswith(";; Function-Def "):
            name = c[0][len(";; Function-Def "):].strip()
        if c[0].startswith("(push)"):
            j = i
            while not chunks[j][0].startswith("(pop)"):
                j += 1
            body = [x for k in range(i, j + 1) for x in chunks[k]]
            label = name or "?"
            seen[label] = seen.get(label, 0) + 1
            if seen[label] > 1:
                label = f"{label}#{seen[label]}"
            items.append(("fn", label, body))
            i = j + 1
            continue
        if c[0].startswith(";"):
            i += 1
            continue
        items.append(("assert" if c[0].startswith("(assert") else "other", None, c))
        i += 1
    return items


def instrument(items, rlimit):
    out, idx = [], []
    for kind, name, body in items:
        if kind != "fn":
            out.append(body)
            continue
        k = len(idx)
        idx.append(name)
        cut = next((n for n, l in enumerate(body) if l.strip() == "(check-sat)"), None)
        if cut is None:
            out.append(body)
            idx.pop()
            continue
        pre = [re.sub(r"\(set-option :rlimit \d+\)", f"(set-option :rlimit {rlimit})", l) if l.strip().startswith("(set-option :rlimit") else l
               for l in body[:cut]]
        out.append(pre + [f' (echo "@@B {k}")', " (get-info :all-statistics)", " (check-sat)", f' (echo "@@E {k}")', " (get-info :all-statistics)", "(pop)"])
    return out, idx


def order(items, seed):
    if seed == 0:
        return items
    rnd, res, run = random.Random(seed), [], []
    for it in items:
        if it[0] == "assert":
            run.append(it)
            continue
        if run:
            rnd.shuffle(run)
            res += run
            run = []
        res.append(it)
    if run:
        rnd.shuffle(run)
        res += run
    return res


def run_z3(items, rlimit, timeout, workdir):
    chunks, idx = instrument(items, rlimit)
    fd, fn = tempfile.mkstemp(suffix=".smt2", dir=workdir)
    with os.fdopen(fd, "w") as fh:
        fh.write("\n".join("\n".join(c) for c in chunks) + "\n")
    try:
        out = subprocess.run(["timeout", str(timeout), "nice", "-n", "10", Z3, "-smt2", fn], capture_output=True, text=True).stdout
    finally:
        os.unlink(fn)
    res, state, cur, before = {}, None, None, None
    for l in out.split("\n"):
        l = l.strip()
        m = re.match(r'@@([BE]) (\d+)', l)
        if m:
            state, cur = m.group(1), int(m.group(2))
            continue
        m = re.search(r":rlimit-count\s+(\d+)", l)
        if m and state:
            if state == "B":
                before = int(m.group(1))
            elif cur in res:
                res[cur][1] = int(m.group(1)) - before
            state = None if state == "E" else state
            continue
        if l in ("sat", "unsat", "unknown") and cur is not None and cur not in res:
            res[cur] = [l, -1]
    return {idx[k]: tuple(v) for k, v in res.items()}, idx


def screen_one(task, args, workdir, parsed):
    path, seed = task
    return path, seed, run_z3(order(parsed[path], seed), args.rlimit, args.timeout, workdir)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--all-eof", action="store_true")
    g.add_argument("--modules", nargs="+")
    g.add_argument("--smt-dir")
    ap.add_argument("--functions", choices=["eof", "all"], default="eof")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--shuffles", type=int, default=8)
    ap.add_argument("--rlimit", type=int, default=30000000)
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--work")
    ap.add_argument("--keep", action="store_true")
    args = ap.parse_args()
    work = args.work or tempfile.mkdtemp(prefix="order-screen.", dir=os.environ.get("TMPDIR"))
    os.makedirs(work, exist_ok=True)
    smt = args.smt_dir
    if not smt:
        smt = os.path.join(work, "smt")
        os.makedirs(smt, exist_ok=True)
        mods = eof_modules() if args.all_eof else args.modules
        print(f"logging {len(mods)} modules into {smt}", file=sys.stderr)
        log_modules(mods, smt, args.threads)
    files = sorted(os.path.join(smt, f) for f in os.listdir(smt) if f.endswith(".smt2"))
    print(f"replaying {len(files)} files x {args.shuffles + 1} orders, {args.jobs} z3 at a time", file=sys.stderr)
    parsed = {p: parse(p) for p in files}
    tasks = [(p, seed) for p in files for seed in range(args.shuffles + 1)]
    results = {}
    with ThreadPoolExecutor(args.jobs) as ex:
        for path, seed, (res, idx) in ex.map(lambda t: screen_one(t, args, work, parsed), tasks):
            per = results.setdefault(path, {})
            for name in idx:
                per.setdefault(name, {})[seed] = res.get(name, ("timeout", -1))
    rows = []
    for path, per in results.items():
        for name, by_seed in per.items():
            rs = [by_seed[k] for k in sorted(by_seed)]
            short = name.split("::")[-1]
            if args.functions == "eof" and not re.search(r"_eo[fl]", short):
                continue
            vals = [r for _, r in rs if r > 0]
            fails = sum(1 for st, _ in rs if st != "unsat")
            spread = max(vals) / min(vals) if vals else 0.0
            rows.append((fails > 0 or spread > 3, fails, spread, name, min(vals or [0]), max(vals or [0]), rs[0][1], len(rs), os.path.basename(path)))
    rows.sort(key=lambda r: (not r[0], -r[1], -r[2], r[3]))
    print(f"{'flag':4} {'fails':>5} {'spread':>7} {'orig':>8} {'min':>8} {'max':>8}  function")
    for flag, fails, spread, name, lo, hi, orig, n, fname in rows:
        print(f"{'!!' if flag else '':4} {fails:>2}/{n:<2} {spread:>7.1f} {orig / 1e6:>7.2f}M {lo / 1e6:>7.2f}M {hi / 1e6:>7.2f}M  {name}  [{fname}]")
    print(f"{sum(1 for r in rows if r[0])} of {len(rows)} functions flagged (any failing order or spread > 3)")
    if not args.keep and not args.work:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
