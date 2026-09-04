# Canonical style

- The entire live `src/kernel/implementation/syscall_alloc_quota/` directory
  is the hand-edited canonical reference. Do not reformat it. Its spec, syscall
  entry, and `commit_alloc_quota_4k` override formatters, old notes, and legacy
  siblings.
- Minimize vertical space in spec, proof, and exec code. Keep one logical
  contract clause per line; keep plain calls, equalities, tuples, and set
  updates intact; put `&&&`/`|||` with the operand.
- Keep short obligations on one line:
  `assert(goal) by { reveal(predicate); };`. No blank padding in braces.
- Rely on NLL through ordinary exec flow; do not add a `{}` scope merely to
  close each mutable borrow immediately. Before an invariant-closing proof,
  or when a real alias/callee conflict requires it, end any live mutable
  reference with a narrow scope or explicit `drop`.
- Contracts and EOF/EOL closure follow the same dense style. Formatting must
  not alter semantics, triggers, reveal order, or proof ownership.
- Keep `requires` bare and proof blocks free of narrating prose. Comments
  explain only a non-obvious contract or soundness boundary.
- Spell out `.view()`; do not add `@` sugar. Use established naming:
  `_4k/_2m/_1g`, `<from>2<to>`, `*_wf`, and `*_requires/*_ensures`.
- `*_spec.rs` files contain specs only. Syscall `mod.rs` files contain only
  declarations; syscall entries stay in `syscall_xxx.rs`; helpers/specs/proofs
  use sibling files prefixed with the module name.

# Proof discipline

- No bare `assert(condition);`, empty `by {}`, proof workaround
  `assume(...)`, `assume(false)`, or `#[verifier::external_body]`.
  Authorized temporary diagnostics must be removed immediately.
- Scope each opaque reveal to the assertion that consumes it. Do not
  redundantly reveal a non-opaque open spec. An EOF S may be opaque-open and
  revealed once at its producer and once per closure VC when fail-on-delete
  requires it. Other function-scope reveals require genuinely shared goals.
- Do not add `assert forall`. Fix the producer trigger/contract instead.
  Exceptions are the approved linked-list/fold patterns and the existing
  quantified lift in
  `lemma_no_change_imply_memory_management_inv_for_page_fields_forall`.
- Approved folds are
  `lemma_{process,thread}_effective_quota_4k_fold_{sum_eq,change_by}_forall`,
  `lemma_process_effective_quota_{2m,1g}_fold_sum_eq_forall`,
  and `lemma_container_thread_quota_folds_insert_zero_forall`. Keep them
  inside the consuming scoped assertion.
- Do not leave bare lemma calls that seed later solver context. Do not add
  operation-specific wrapper/framing lemmas or proof-only snapshots. A snapshot
  is allowed only when a real transition consumes the old dynamic lock id.
- New generic Set/Seq/Map algebra lemmas may follow existing patterns. Ask
  before adding a lemma specialized to a repository-defined type.
- Never broadcast `vstd::set::group_set_lemmas`; activate narrow lemmas only.
  Do not change common invariant/lemma triggers unless explicitly authorized.
- Deep quantified invariants use deliberate lookup-chain triggers. Shallow
  single-entry framing may use `#![auto]`. Never add `#![all_triggers]` or
  call-site quantified scaffolding to compensate for a bad trigger.
- Keep separate positive pre- and post-state triggers on all
  `*_unchanged_except` families. A joint trigger is not equivalent.
- Rebuild only invariant leaves whose inputs changed, with scoped reveals and
  direct operation facts. Use subsystem -> memory -> process -> direct leaves
  -> `inv()` order.
- Keep `*_perms_wf` opaque. Keep map-wide framing/unlocked predicates opaque
  by default. Open a conjunction wrapper only after checking nested quantified
  expansion and focused/full measurements.
- Once green, delete every added assert, reveal, lemma call, and ghost one at a
  time; retain only fail-on-delete proof. Preserve measured reveal order.
- `#[verifier::spinoff_prover]` is wall-time scheduling only. Add, remove, or
  move it after paired same-scope wall measurements. Ignore rlimit for this
  decision.
- Prefer direct operation facts. Do not hide a hard callsite inside a new helper
  or split equations merely for prover parallelism.
