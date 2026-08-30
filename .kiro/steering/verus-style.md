# VeriFlat Verus style

`AGENTS.md` is authoritative. This file is a short surface-style checklist.
The entire live `src/kernel/implementation/syscall_alloc_quota/` directory is
the hand-edited canonical example; do not reformat it. Canonical code wins over
this checklist.

## Layout

- Minimize vertical space. Keep one logical contract clause per line and keep
  plain calls, equalities, tuples, and set operations intact.
- Put `&&&`/`|||` on the operand line. Keep short
  `assert(goal) by { reveal(...); };` blocks on one line.
- Rely on NLL in ordinary exec flow. Use a narrow scope or explicit `drop`
  only before invariant closure or for a real alias/callee conflict.
- Keep `requires` and ordinary proof blocks free of narration. Comment only a
  non-obvious contract or soundness boundary.
- Spell out `.view()`; do not add `@` syntax.

## Specs and proofs

- Use established names: `*_wf`, `*_requires/*_ensures`,
  `<from>2<to>`, and `_4k/_2m/_1g` families.
- Use deliberate deep lookup triggers, `#![auto]` only for shallow
  single-entry framing, and never `#![all_triggers]`.
- Do not compensate for trigger gaps with call-site `assert forall`.
- Scope opaque reveals to consuming assertions. Rebuild nested invariants in
  subsystem -> memory -> process -> direct -> `inv()` order.
- No bare asserts, empty `by {}`, dead ghosts, duplicate reveals, proof
  workarounds, or one-caller framing wrappers.
- After verification, delete proof scaffolding one item at a time and keep only
  fail-on-delete material.
- Treat `spinoff_prover` only as a paired wall-time decision; ignore rlimit.

## Files and contracts

- Spec files contain specs only. Syscall entries and helpers use the directory
  layout required by `AGENTS.md`.
- State exact operation results and needed framing; use
  `unchanged_except` for a touched map/array entry.
- Use `map.lock_id_by_key(key)` and `array.lock_id_by_index(index)`; do not
  hand-build dynamic lock ids.
- Follow the slow-equation S/EOF exception in `AGENTS.md` exactly. S is only
  entry facts plus exact delta; EOF framing calls are only approved
  no-change-WF and fold lemmas.
