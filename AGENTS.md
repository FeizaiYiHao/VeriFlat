# VeriFlat repository rules

This is the repository-level source of truth for Codex. Live code wins over
older notes. Preserve the user's dirty worktree and unrelated edits.

## Scope and semantics

- Read this file before editing. Subagents receive explicit file ownership and
  report changed files plus verification run numbers.
- Do not reset, overwrite, restage, or clean unrelated changes. Freeze shared
  APIs before parallel verification.
- Diagnose questions read-only. Implement only when asked. If a proof exposes
  an unclear invariant or semantic mismatch, report it before changing the
  model. Do not invent preconditions, runtime checks, representations, or
  framing bridges.
- A direct postcondition may expose an operation's existing narrow guarantee.
  Preconditions stay limited to safety, semantics, and direct callees.
- Invariants and cross-function contracts must not use `exists` or `choose` to
  hide objects. Pass concrete arguments and results. Choices used only inside
  a proof for indices, counterexamples, or induction remain allowed.
- After changing a contract, simplify its callers' old proofs and verify which
  facts are still necessary. Use typed lock maps directly for lock membership
  and scope; preserve the approved relations described by the kernel-model skill.
- Before introducing a new framing spec or framing lemma, obtain explicit user
  approval for that specific abstraction. Show its proposed name, complete
  definition or lemma statement, objects and fields preserved, intended use
  sites, and why direct proof or existing relations are insufficient. Reuse,
  performance, and slow-equation EOF/EOL summaries do not waive approval.
  Names must identify what is preserved. Permission to retain an existing spec
  or lemma does not authorize a new one.
- Ordinary edits to a function's `requires` and `ensures` do not require
  separate approval, including clauses that state which fields or lock-map
  entries are preserved. Do not classify a normal contract edit as a new
  framing spec merely because it relates old and new states. This does not
  authorize introducing a new framing helper or abstraction.
- Delete dead private helpers after checking callers. Public syscalls and
  intended public primitives are not dead merely because they lack in-tree
  callers.
- There is no fixed acceptable wall-time regression. Follow the build skill's
  measurement rules and bring a persistent slowdown beyond observed variation
  to the user with the concrete simplification and measurements.
- Report verification and proof-performance results in the conversation. Do
  not retain verification reports, handoff records, run logs, profiles, or
  benchmark source snapshots. Temporary measurement files must be removed
  before handoff; the shared verification run counter may remain.

## Required repository skills

The detailed rules live in repository-owned skills so unrelated turns do not
load them. Use every matching skill before acting, and read only the references
that its `SKILL.md` routes to for the current task.

- Use `$veriflat-kernel-model` for locks, `LocalContext`, kernel transitions,
  `mmap_4k`, IPC, and the current syscall model.
- Use `$veriflat-proof` for Verus spec/proof/exec edits or reviews, proof
  debugging, invariant closure, trigger work, or proof-performance changes.
- Use `$veriflat-build` for crate/module/API boundaries, Cargo-Verus workspace
  changes, verification runs, measurements, and final handoff.

The canonical skill sources are under `.codex/skills/`. If a fresh Codex
process has not discovered one yet, open its `SKILL.md` there directly and
follow the same routing.
