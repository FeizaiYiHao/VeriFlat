# Verification and handoff

- In Windows-hosted sessions run builds in WSL at
  `/home/xiangdc/VeriFlat`.
- During development, use the split Cargo-Verus workspace. Start with
  `./verify-workspace.sh --package <package>` and narrow further with
  `--verify-only-module`/`--verify-function` when appropriate. Do not use the
  monolithic build for routine proof iteration; reserve it for final
  cross-crate closure and same-scope performance measurements.
- Changing only Verus CLI selection or profiling arguments may reuse a Cargo
  artifact produced with earlier arguments. If a real cold rerun is required,
  invalidate only the affected package under `target/verus-partial`; never
  treat a cached no-op as fresh verification.
- Focused/workspace: `./verify-workspace.sh --package <package>` and
  `./verify-workspace.sh`. Monolith:
  `./verify.sh --num-threads 32 --time`. Report each run number.
- Pipeline measurement:
  `VERUS_PIPELINE_SMT=1 verus/source/target-verus/release/cargo-verus verify --workspace --exclude VeriFlat -- --num-threads 32 --time`.
  Use Cargo's default concurrency. Label vstd and every VeriFlat artifact
  independently hot/cold; a fully cached no-op is not a benchmark.
- Typecheck first, then verify the smallest function/module/package. Completed
  cross-crate work requires full workspace and 32-thread monolith checks.
- Treat >50 seconds as suspicious. Performance reports include Rust, VIR,
  verification, SMT, wall, and rlimit under identical cache/thread scope.
  Rlimit alone does not determine proof speed.
- Preserve the permanent build architecture and do not hand off new warnings.
- Before handoff run `git diff --check` and a style audit only on files changed
  in this session. Check bare/empty asserts, `assert forall`, loose reveals,
  assumes, dead ghosts, duplicate reveals, and new wrappers. Exclude pre-existing
  dirty files and the canonical `syscall_alloc_quota/` directory.
- The Codex hooks in `.codex/hooks.json` enforce a session-level two-pass
  reminder/gate for changed Rust files; they do not certify proof correctness.
