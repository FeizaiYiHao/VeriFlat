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
- Blocks with local `let` bindings are always multiline, across the entire
  repository's spec, contract, proof, and exec code. Put the opening brace,
  each `let` statement, each `&&&`/`|||` clause, and the closing brace on
  separate lines. Keep each binding's expression compact; do not compress
  multiple bindings or the following conditions onto one line. This takes
  precedence over the short-block rule above.
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

- Step-wrapper preconditions accept only concrete K-layer facts: kernel state,
  local context, typed lock maps, and K-layer operation relations. Do not require
  U projections, U field facts, or U step/trace predicates, directly or through
  a helper. Wrapper bodies and postconditions may derive generic K-to-U facts
  and record traces, but must not depend on syscall-specific step predicates.
  Keep generic K-to-U lemmas in the step-wrapper layer
  (`kernel_step_wrappers.rs`, `src/kernel/kernel_step_wrappers/`); they never
  mention a syscall-specific step predicate, which crate dependencies forbid.
  These need no approval.
- Exec equations and their own contracts contain no U reasoning. Do not reveal a
  U step, step_pre, trace, or result spec; call a K-to-U projection lemma
  (`*_projection_at`, `kernel_write_held_context_projection`, ...); call
  `use_type_invariant(&*steps)`; build `ThreadU{..}`/`KernelU{..}` literals or
  `kernel_k_to_kernel_u(..).x =~= ..` compositions; or put field-level
  `kernel_k_to_kernel_u(..)`/`kernel_k_to_nonlock_kernel_u(..)` clauses in an
  exec fn's requires/ensures. Exec holds K facts and calls wrapper-layer K-to-U
  step lemmas, step-boundary wrappers, and the operation's trace lemmas. The only
  U in exec contracts is the public syscall trace/result ensures stated on
  `steps.view()`/`nonlock_view()`, or on a whole
  `kernel_k_to_kernel_u(*old(krnl))` or `*final(krnl)` passed to a trace or
  result spec.
- Exec equations are K-only transition proofs. An exec equation holds concrete
  K facts, establishes S (which map entries and lock states changed) and
  typed-lock-map alignment, and proves its callees' preconditions. It closes no
  invariant and reasons about no U state. Hence it never contains
  `reveal(<...>_wf)`, `reveal(<...>_inv)`, or a K-to-U construct: invariant
  closure lives in the operation's EOF closure functions (every mutating
  equation gets one), and K-to-U lives in the step-wrapper layer and
  `*_trace.rs`. The only invariant use allowed in exec is a point fact a
  callee's precondition needs, obtained from a `*_wf_at` point lemma or a
  callee's ensures, never from a reveal. A point fact the exec cannot obtain
  that way is a producer-contract gap: add the ensures to the producer or add a
  `*_wf_at` point lemma (approval-free, like fold lemmas) instead of revealing
  in exec. Lock/unlock primitives (`locker_unlocker/`) are exec equations too
  and follow the same rule.
- `*_wf_at` point lemmas have one shape: `requires <pred>_wf(<maps>)` plus the
  index's domain membership, `ensures` only the quantified body instantiated at
  that index, body `reveal(<pred>_wf)`. They never ensure a map-level or
  quantified fact (`perms_wf()`, `inv()`, a forall); such a clause leaks the
  invariant into the caller's context and is a defect to fix in the lemma, not a
  convenience. Call a `*_wf_at` in exec only to discharge a callee's
  precondition; a fact the just-executed callee can state goes in that callee's
  ensures instead. Without the full-EOF boundary a `*_wf_at` chain in exec is
  piecewise invariant closure, which is the same leak as a reveal: add the EOF
  boundary first. A map-level fact comes from the matching `*_wf_map` lemma
  (`requires <pred>_wf(<maps>)`, `ensures` only `perms_wf()` or `.inv()`),
  called only where that fact is needed.
- Operation-local K-to-U bridging lemmas live in the operation's `*_trace.rs` and
  need no approval: `<op>_<step>_pre_from_k(krnl, lctx, cpu_id, ..)` requires
  only K facts the exec already holds and ensures the op's U step_pre on
  `kernel_k_to_kernel_u(*krnl)`; `<op>_<step>_from_u(pre_u, [mid_u,] post_u, ..)`
  requires verbatim the wrapper K-to-U lemma ensures form(s) and ensures the op's
  U step; `<op>_result_from_k(krnl, cpu_id, .., ret)` ensures the op's result
  spec; plus trace-composition lemmas. Their requires are K facts or wrapper
  ensures verbatim, their ensures are existing U specs of that operation, and
  their bodies hold only projection calls, reveals, `use_type_invariant`, and
  `assert_maps_equal!`. They introduce no new spec. List every one added in the
  report.
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
- EOF naming. The operation-state summary S of a full-EOF equation and every
  framing spec or lemma that exists only for an EOF closure carry `eof` in their
  name: S is `<op>_eof_transition_framing` (e.g.
  `create_process_from_staged_pages_eof_transition_framing`), EOF-only helper
  framing is `<op>_eof_<what>`. S holds only transition/framing facts: which map
  entries, pages, and lock states changed and what stayed equal. The
  operation's preconditions stay in the exec contract's `requires`, not in S. S
  lives in the operation's `*_eof*.rs` or `*_spec.rs` file, never in the exec
  file. Framing names outside EOF state what is preserved (`held_*_unchanged`,
  `kernel_*_nonlock_fields_unchanged`); names that do not, such as
  `*_framed_fields_equal` or `*_kernel_state_framing`, are to be renamed.
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
  `retype_4k_page_perm_to_allocator`, `retype_4k_page_perm_to_scheduler`,
  `retype_page_perm_2m_to_rwlock`, `retype_page_perm_to_rwlock`,
  `retype_container_page_tail_to_offline_flags`, and the inverses
  `retype_thread_rwlock_to_4k_page_perm`,
  `retype_process_rwlock_to_4k_page_perm`, and
  `retype_endpoint_rwlock_to_4k_page_perm` (an exclusively held lock object
  back to its owned 4K page permission: an unreferenced thread, a killed
  childless and threadless process, or an unqueued endpoint whose last
  descriptor reference is gone). Keep those primitives limited to consuming an
  owned page permission and constructing the corresponding kernel object, or
  the exact inverse for thread exit, process reclaim, or endpoint release;
  new variants or callers require explicit authorization. The other approved
  trusted primitives are the hardware TLB invalidations
  `CpuTLB::flush_all_local_pcids` and `IommuTLB::invalidate_domain`.
  Authorized temporary diagnostics must be removed immediately.
- Treat existing `external_body` contracts, mathematical axioms, and permission
  construction with `Tracked::assume_new()` as trust boundaries. Do not replace
  a failed proof with these mechanisms or `assume_specification`. Changes to
  established TCB contracts or additional trusted construction paths require
  specific user authorization; zero explicit assumptions does not mean zero trust.
- Scope each opaque reveal to the assertion that consumes it. Do not add a
  reveal of a non-opaque open spec to new proof. An existing one is not a
  semantic no-op at the SMT level: Verus encodes every `reveal(f)` as the
  ground fact `(assume (fuel_bool fuel%f))`, which lets the definition axiom
  fire one E-matching round earlier than deriving it through the
  `fuel_defaults` quantifier. Removing such a reveal is a deletion test like any
  other hint (both verification modes, rlimit compared against a baseline), not
  a free cleanup; e.g. `eof_container_uppertree_seq_wf` fails without its two
  `reveal(KernelK::inv)`. An EOF S may be opaque-open and revealed once at its
  producer and once per closure VC when fail-on-delete requires it. Other
  function-scope reveals require genuinely shared goals.
- Do not add `assert forall`. Fix the producer trigger/contract instead.
  Exceptions are the approved linked-list/fold patterns and the existing
  quantified lift in
  `lemma_memory_management_inv_preserved_for_page_invariant_fields_forall`.
- Approved folds are
  `lemma_{process,thread}_effective_quota_4k_fold_{sum_eq,change_by}_forall`,
  `lemma_process_effective_quota_{2m,1g}_fold_sum_eq_forall`,
  `lemma_thread_effective_quota_2m_fold_{sum_eq,change_by}_forall`,
  `lemma_thread_effective_quota_1g_fold_sum_eq_forall`,
  `lemma_thread_pending_{4k,2m,1g}_folds_eq_forall`,
  `lemma_thread_pending_4k_folds_change_by_forall`,
  `lemma_container_process_thread_quota_folds_insert_zero_forall`, and the closure
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
  decision. It is never a fix for a flaky or unstable proof (user rule
  2026-10-12): diagnose the trigger/context cause and repair the proof.
- Prefer direct operation facts. Do not hide a hard callsite inside a new helper
  or split equations merely for prover parallelism. Splitting is appropriate
  when required to isolate solver context or bring a >10-second equation below
  the repository limit.
