---
description: Review this session's Verus edits against AGENTS.md and the canonical syscall_alloc_quota directory
---

Review only `src/**/*.rs` files recorded in
`.claude/.session-edits`. Ignore pre-existing dirty files and any path no
longer dirty. If `$ARGUMENTS` supplies a base ref, diff against it; otherwise
use `HEAD`.

Read `AGENTS.md`, `.kiro/steering/verus-style.md`, and the live
`src/kernel/implementation/syscall_alloc_quota/` directory. Check:

- canonical dense layout in spec/proof/exec contracts and bodies;
- no live mutable reference at invariant closure or an aliasing callee;
- bare `requires`, comment-free ordinary proof blocks, and no `@` sugar;
- no bare assert, empty `by {}`, unapproved/call-site `assert forall`, loose reveal, assume,
  dead ghost, duplicate reveal, or new wrapper/framing lemma;
- deliberate triggers, never `#![all_triggers]`;
- nested invariant closure and the S/EOF restrictions in `AGENTS.md`;
- paired wall-time evidence for any spinoff change;
- correct syscall/module file placement.

Report each finding as `path:line - issue -> fix`, then end with `clean` or
`N violations`. This command is review-only unless `--fix` is supplied.

On a clean pass, certify exactly the reviewed dirty files in
`.claude/.style-checked` as one
`<git-hash-object><TAB><path>` line per file. If none remains dirty, certify
an empty file. Do not update the sentinel when violations remain. With
`--fix`, apply fixes, run the smallest relevant verification, review again,
and certify only after it is clean.
