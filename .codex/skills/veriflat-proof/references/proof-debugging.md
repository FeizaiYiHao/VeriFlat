# Proof debugging

- Reproduce the first failure with the smallest function/module command before
  changing proof shape. Classify it as a missing semantic fact, producer shape,
  trigger/reveal issue, or resource cost.
- Before calling an invariant structurally hard to close, supply the existing
  operation facts, scoped reveals, and generic Set/Seq/Map or approved fold facts.
  A missing algebra or lookup fact is a proof-fact gap. Report an actual semantic
  mismatch before changing the model; do not pass the desired post invariant as
  a precondition or hide its closure inside an operation-specific wrapper.
- For a suspected trigger crutch, delete the call-site `assert forall` and
  reverify. If it fails, move only any buried reveals into the consuming
  assertion and retry; report a trigger gap only after that still fails.
- For an opaque `*_wf` or unmet `recommends`, temporarily assert its
  conjunction, then bisect conjuncts to find the first missing dependency.
  Move the minimal reveals/facts to the real scoped goal and remove the
  expanded diagnostic.
- Delete suspected asserts, reveals, and ghosts one at a time. A failure after
  deleting a block may mean a nested reveal was lost, not that the block's
  quantified conclusion was necessary.
- After changing result or constructor contracts, revisit the callers' old tail
  assertions, state rechecks, lemma calls, and history snapshots. Test deletion
  before adding more scaffolding. A more direct contract changes solver search;
  it does not guarantee that the old proof remains efficient.
- If several branches need the same fact, prove it once at a common point where
  it holds and subsequent callee guarantees preserve it. Keep the reveal scoped
  to that assertion. Verify that later mutations or interleaving cannot invalidate
  it, and retain only facts required by deletion tests.
- Diagnose cumulative cost with identical cache/thread scope and successive
  semantic boundaries. Use a temporary `assume(false)` cutoff only with
  explicit authorization, one cutoff at a time, and restore it immediately.
- Record the focused run number and SMT/wall/rlimit for each retained proof or
  scheduling change. Never leave diagnostic scaffolding in the tree.
