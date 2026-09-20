---
description: Review this session's VeriFlat source edits against canonical rules
---

Review only dirty `src/**/*.rs` paths recorded in `.claude/.session-edits`.
Ignore pre-existing dirty files the session did not touch. If `$ARGUMENTS`
supplies a base ref, diff against it; otherwise use `HEAD`.

Read:

- `AGENTS.md`;
- `.codex/skills/veriflat-proof/references/style-and-discipline.md`;
- `.codex/skills/veriflat-build/references/verification.md`;
- the live hand-edited `src/kernel/implementation/syscall_alloc_quota/`
  directory as a style reference.

Check the exact session-edited files for contract/layout consistency, live
mutable references at invariant closure, bare or empty assertions, call-site
`assert forall`, loose reveals or lemma calls, assumptions, dead ghosts,
duplicate scaffolding, trigger discipline, new wrappers, and EOF restrictions.
The canonical example directory is reviewed normally if this session changed
it; it is not immutable or excluded.

Report each finding as `path:line - issue -> fix`, then end with `clean` or
`N violations`. This command is review-only unless `--fix` is supplied.

On a clean pass, certify exactly the reviewed dirty files in
`.claude/.style-checked` as one `<git-hash-object><TAB><path>` line per file.
Do not update the sentinel while violations remain. With `--fix`, apply fixes,
run the smallest relevant verification, review again, and certify only after
the resulting content is clean.
