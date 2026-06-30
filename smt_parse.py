#!/usr/bin/env python3
"""Parse Verus --output-json --time output, list per-function SMT time sorted."""
import json
import sys


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else ".smt_times.json"
    with open(path) as f:
        d = json.load(f)
    mods = d.get("times", {}).get("smt", {}).get("smt-run-module-times", [])
    rows = []
    for m in mods:
        for fn in m.get("function-breakdown", []):
            rows.append((
                fn.get("time-micros", 0) / 1000.0,   # ms
                fn.get("rlimit", 0),
                fn.get("success", True),
                fn.get("mode:", fn.get("mode", "")),
                fn["function"],
            ))
    rows.sort(key=lambda r: r[0], reverse=True)

    total_ms = sum(r[0] for r in rows)
    print(f"{'SMT(ms)':>9}  {'rlimit':>10}  ok  {'mode':<5}  function")
    print("-" * 90)
    for ms, rl, ok, mode, name in rows:
        print(f"{ms:9.1f}  {rl:10d}  {'Y' if ok else 'N':>2}  {mode:<5}  {name}")
    print("-" * 90)
    print(f"{total_ms:9.1f}  {'':>10}      {'':<5}  TOTAL over {len(rows)} functions")


if __name__ == "__main__":
    main()
