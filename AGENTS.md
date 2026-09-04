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
- Delete dead private helpers after checking callers. Public syscalls and
  intended public primitives are not dead merely because they lack in-tree
  callers.

## Required repository skills

The detailed rules live in repository-owned skills so unrelated turns do not
load them. Use every matching skill before acting, and read only the references
that its `SKILL.md` routes to for the current task.

- Use `$veriflat-kernel-model` for locks, `LocalContext`, kernel transitions,
  `mmap_4k`, IPC, and the current syscall model.
- Use `$veriflat-proof` for Verus spec/proof/exec edits, proof debugging,
  invariant closure, trigger work, or proof-performance changes.
- Use `$veriflat-build` for crate/module/API boundaries, Cargo-Verus workspace
  changes, verification runs, measurements, and final handoff.

The canonical skill sources are under `.codex/skills/`. If a fresh Codex
process has not discovered one yet, open its `SKILL.md` there directly and
follow the same routing.
