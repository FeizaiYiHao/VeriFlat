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
- Use `--time-expanded` to inspect equation-level cost. A structurally large
  equation may justify a higher `--rlimit` or `#[verifier::rlimit]`; high rlimit
  alone does not determine proof quality or speed. Measure the uncapped cost,
  report the old and new ceilings, and use the smallest practical ceiling.
- Any single verification equation exceeding 10 seconds of SMT time is
  abnormal. Diagnose accumulated context, producer/trigger shape, quantifier
  expansion, and proof boundaries; simplify, isolate, or split the equation
  before handoff. Do not use a higher rlimit to excuse a >10-second equation.
  Performance reports include Rust, VIR, verification, SMT, wall, and rlimit
  under identical cache/thread scope.
- For comparisons, freeze the source versions and keep the binary, arguments,
  threads, source path, and artifact reuse equivalent; disclose unavoidable
  differences. Interleave baseline/candidate runs, include every sample in the
  comparison, and avoid concurrent heavy verification. Report observed variation
  and repeat as needed before treating a slowdown or speedup as reproducible.
- Report results in the conversation. Do not retain verification reports,
  handoff records, run logs, profiles, or benchmark source snapshots. Use
  temporary files while measuring and remove them before handoff. Keep only
  the shared run counter, not a persistent history of commands or results.
- Label function-body SMT, independently verified callees, package wall, and
  whole-workspace/monolith wall separately. A call-chain cost must include its
  constituent obligations, with shared callees counted once. Sum all independent
  entries for a function when aggregating profiles. Parallel SMT times are not
  wall time, and a local rlimit reduction is not evidence of whole-build speedup.
- There is no automatic wall-time regression allowance. First adapt the proof
  and repeat the comparison. If a slowdown persists beyond observed variation,
  present the concrete simplification and measurements for a user decision.
  When measurements remain noisy, report that uncertainty rather than claiming
  the regression is resolved. Historical per-batch tolerances are not defaults.
- Preserve the permanent build architecture and do not hand off new warnings.
- Before handoff run `git diff --check` and a style audit only on files changed
  in this session. Check bare/empty asserts, `assert forall`, loose reveals,
  assumes, dead ghosts, duplicate reveals, and new wrappers. Exclude pre-existing
  dirty files. Use the hand-edited `syscall_alloc_quota/` directory as a style
  reference, not as an immutable or excluded path.
- The Codex hooks in `.codex/hooks.json` enforce a session-level two-pass
  reminder/gate for changed Rust files; they do not certify proof correctness.
