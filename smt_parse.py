#!/usr/bin/env python3
"""Report measured Verus JSON results; reject missing or unverified output."""
import argparse
import json
from pathlib import Path
import sys


def report(data, modules=False, threshold_ms=0):
    times = data["times-ms"]
    result = data["verification-results"]
    smt = times["smt"]
    mods = smt["smt-run-module-times"]
    rows = []
    for m in mods:
        for fn in [m] if modules else m.get("function-breakdown", []):
            rows.append((
                fn["time-micros"] / 1000.0,
                fn["rlimit"],
                fn.get("success", True),
                fn.get("mode:", fn.get("mode", "")),
                fn["module" if modules else "function"],
            ))
    rows.sort(key=lambda r: r[0], reverse=True)

    if not rows:
        raise ValueError("no measurements; cached or unverified output is not a benchmark")
    print(f"{'SMT(ms)':>9}  {'rlimit':>10}  ok  {'mode':<5}  {'module' if modules else 'function'}")
    for ms, rl, ok, mode, name in rows:
        if ms > threshold_ms or not ok:
            print(f"{ms:9.1f}  {rl:10d}  {'Y' if ok else 'N':>2}  {mode:<5}  {name}")
    print(f"TOTAL SMT {sum(r[0] for r in rows):.1f} ms over {len(rows)} measured rows")
    print(f"Rust {times['rust']['total']} ms; VIR {times['verification']['vir']['total']} ms; "
          f"verification {times['verification']['total']} ms; SMT run {smt['smt-run']} ms; "
          f"Verus wall {times['total']} ms; rlimit {smt['rlimit-run']}; threads {times['num-threads']}")
    print(f"Verified {result['verified']}; errors {result['errors']}; entire crate {result['is-verifying-entire-crate']}")
    return bool(result.get('success')) and result['errors'] == 0 and all(r[2] for r in rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('path', type=Path)
    parser.add_argument('--modules', action='store_true')
    parser.add_argument('--threshold-ms', type=float, default=0)
    args = parser.parse_args()
    try:
        return 0 if report(json.loads(args.path.read_text()), args.modules, args.threshold_ms) else 1
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f'timing report unavailable: {exc}', file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
