# Canonical style

- The entire live `src/kernel/implementation/syscall_alloc_quota/` directory
  is the hand-edited canonical reference. Do not reformat it. Its spec, syscall
  entry, and `commit_alloc_quota_4k` override formatters, old notes, and legacy
  siblings.
- Minimize vertical space in spec, proof, and exec code. Keep one logical
  contract clause per line; keep plain calls, equalities, tuples, and set
  updates intact; put `&&&`/`|||` with the operand.
- Pack function parameters, call arguments, tuple elements, and set/seq/map
  literal elements into compact readable groups. Do not default to one item per
  line, and do not force a long signature, call, tuple, or literal onto one
  enormous line; wrap it across the fewest balanced lines that remain readable.
- Never staircase one accessor chain, comparison, implication, arithmetic
  expression, or logical clause across lines. Keep it intact on one line when
  practical; if it must wrap, do so at a real semantic boundary rather than
  before each `.view()`, operator, or operand.
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

# Contracts and concrete results

- Describe an operation through its concrete inputs and results. Constructors
  may expose the exact value they already construct, including a deterministic
  ghost sequence, so consumers can use that fact across crate boundaries.
  New framing specs and framing lemmas require the specific approval defined
  in `AGENTS.md`. Ordinary `requires`/`ensures` edits do not require separate
  approval, including direct preservation guarantees. The operation-specific
  complete S and independent closure functions for full EOF of a long equation
  are the documented exception: they need no separate approval and S may be
  reshaped freely within the semantic and proof-boundary constraints in
  `AGENTS.md` and `slow-equation.md`.
- Keep preconditions limited to safety, semantics, and direct callees. Before
  removing a parameter, inspect exec uses, proof consumers, and dependencies
  across kernel-step boundaries; an argument unused by exec may still be needed.
- Remove duplicate or implied contract clauses and separately approved unused
  guarantees. Preserve semantic guarantees; absence of an in-tree consumer alone
  does not authorize weakening a public contract. Avoid repeating immutable
  input facts in postconditions when the existing interface already supplies them.
- Do not introduce `exists` or `choose` in specs, contracts, or proofs,
  including through a helper spec. Use explicit arguments, return fields, known
  indices, deterministic constructions, repaired producer contracts, or repaired
  triggers instead.

# Proof discipline

- No bare `assert(condition);` or empty `by {}`. Do not leave `assume(...)`,
  `assume(false)`, or `admit()` in delivered proof code. Temporary diagnostic
  cutoffs require the explicit authorization and immediate restoration described
  in [proof-debugging.md](proof-debugging.md).
- Do not add `#[verifier::external_body]`
  outside the explicitly approved page-retype TCB boundary:
  `retype_4k_page_perm_to_allocator` and
  `retype_page_perm_2m_to_rwlock`. Keep those primitives limited to consuming
  an owned page permission and constructing the corresponding kernel object;
  new variants or callers require explicit authorization. Authorized temporary
  diagnostics must be removed immediately.
- Treat existing `external_body` contracts, mathematical axioms, and permission
  construction with `Tracked::assume_new()` as trust boundaries. Do not replace
  a failed proof with these mechanisms or `assume_specification`. Changes to
  established TCB contracts or additional trusted construction paths require
  specific user authorization; zero explicit assumptions does not mean zero trust.
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
  `lemma_thread_effective_quota_2m_fold_{sum_eq,change_by}_forall`,
  `lemma_thread_pending_{4k,2m}_folds_eq_forall`,
  `lemma_container_thread_quota_folds_insert_zero_forall`, and the closure
  bridges `lemma_process_effective_quota_folds_singleton`,
  `lemma_thread_quota_folds_empty`, and
  `lemma_process_effective_quota_folds_insert_zero` (they absorb the
  `value_fold =~= direct_fold` extensionality step once). Keep them inside the
  consuming scoped assertion.
- Do not leave bare lemma calls that seed later solver context. Do not add
  operation-specific wrappers, unapproved framing specs or framing lemmas, or
  proof-only snapshots. A snapshot
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
  or split equations merely for prover parallelism. Splitting is appropriate
  when required to isolate solver context or bring a >10-second equation below
  the repository limit.
