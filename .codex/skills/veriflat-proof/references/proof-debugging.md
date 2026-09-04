# Proof debugging

- Reproduce the first failure with the smallest function/module command before
  changing proof shape. Classify it as a missing semantic fact, producer shape,
  trigger/reveal issue, or resource cost.
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
- Diagnose cumulative cost with identical cache/thread scope and successive
  semantic boundaries. Use a temporary `assume(false)` cutoff only with
  explicit authorization, one cutoff at a time, and restore it immediately.
- Record the focused run number and SMT/wall/rlimit for each retained proof or
  scheduling change. Never leave diagnostic scaffolding in the tree.
