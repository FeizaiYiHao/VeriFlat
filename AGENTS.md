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

### Lock model

- `LocalContext` has typed held-lock maps plus one exact pair ledger:
  `Set<(LockId, KernelObjId)>`. Do not add object-only sets, scalar lock-id
  sets, or another pair ledger.
- `typed_lock_maps_aligned(k, lctx)` aligns each physical object family with
  its typed map. `lock_id_set_aligned(lctx)` aligns typed entries with exact
  `(id, object)` pairs; lock mode is represented only in the typed maps.
- Acquire inserts the exact typed entry and current pair; unlock removes both;
  a dynamic-id change overwrites the typed entry and replaces the pair during
  the transition. Producers close both alignments at their wrapper boundary.
- Lock membership, counts, scopes, and finish conditions read typed maps.
  Deadlock checks and major bounds quantify only the exact pair set. Syscalls
  and transitions do not reveal either alignment or rebuild it manually.
- Thread ownership metadata never disappears. Running, scheduled, and blocked
  states use their established dynamic lock-id majors; `NotApp` changes only
  lock ordering and does not restrict IPC topology.
- Do not infer local lock state backwards from alignment. Lower-level lock
  operations should expose target state, id changes, ledger changes, and
  unchanged fields directly.
- At a kernel-step boundary, frame held objects explicitly. Preserve
  `all_objects_unlocked` directly rather than deriving it from an empty ledger.

### Current syscall semantics

- `mmap_4k` keeps the `quota == range * 4` precheck, uses hierarchical
  range-clean predicates, builds page-table levels, then installs executable 4K
  leaves. Do not restore the deleted legacy mmap path.
- Ordinary IPC supports Empty and Pages for send/receive. Pages shares existing
  4K data mappings and allocates only missing receiver page-table directories.
  Call/reply and other non-empty payloads remain out of scope.
- SEND queues contain only SENDING/CALLING; RECEIVE queues contain only
  RECEIVING/RECEIVING_CALL. Same-direction or empty queues block with the exact
  payload. Opposite-direction handling locks the peer first.
- Pages rendezvous validates type, equal length, distinct processes, source and
  target ranges, quota, and ownership before mutation. Errors preserve queue,
  mapping, and quota state. Queue length and refcount remain one `usize` each.

## Canonical style

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

## Proof discipline

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

### Proof debugging

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

### Slow-equation EOF/EOL exception

- A function or loop whose single equation exceeds 5 seconds SMT under
  `--time-expanded` may use one S-shaped EOF/EOL summary.
- Define exactly one open spec, optionally `#[verifier::opaque]` for solver
  scheduling: `<operation>_transition_framing`. It contains only entry facts, exact
  pre-to-post mutation/framing, and necessary argument identities. It contains
  no post invariant, post `*_wf`, permission-WF, or derived closure result;
  inline subordinate relations instead of defining more specs.
- Prove S at the mutation producer from constructor/update/callee facts. One
  scoped reveal opens opaque S; do not unfold `KernelK::inv`, subsystem
  invariants, or old invariant leaves merely to state it. Keep
  `typed_lock_maps_aligned` and `lock_id_set_aligned` in exec.
- EOF closure may split only its invariant-closing tail into small proof
  blocks/functions. Framing calls there are limited to existing
  `lemma_no_change_imply_*_wf*` and approved fold lemmas. All other new or
  existing specialized preservation/framing helpers are forbidden; prove
  changed-state leaves inline with S, scoped reveals, and direct algebra.
- Closure still follows subsystem -> memory -> process -> direct leaves ->
  `inv()`, and uses the canonical compact layout.

## Architecture

- Preserve the monolithic `src/lib.rs` build and the split Cargo-Verus
  workspace over the same live sources.
- Dependency order is:
  `kernel_core -> alloc_page -> {new_thread, map_4k}`;
  `map_4k -> {mmap_4k, ipc}`; `kernel_core -> alloc_quota`.
  Syscall crates are terminal and never depend on another syscall crate.
- Kernel core owns shared definitions, invariants, lemmas, locks, primitives,
  and release/finish operations. Allocation, mapping, and syscalls stay in
  their dedicated crates.
- Use ordinary module resolution, private terminal dependency imports, and the
  `split-crates` feature. Do not add `#[path]` roots or Cargo/monolith source
  forks.
- Cross-crate needs make the original item public or convert the original
  method to a standalone function; do not invent bridge lemmas.

## Verification and handoff

- In Windows-hosted sessions run builds in WSL at
  `/home/xiangdc/VeriFlat`.
- Focused/workspace: `./verify-workspace.sh --package <package>` and
  `./verify-workspace.sh`. Monolith:
  `./verify.sh --num-threads 32 --time`. Report each run number.
- Pipeline measurement:
  `VERUS_PIPELINE_SMT=1 verus/source/target-verus/release/cargo-verus verify --workspace --exclude VeriFlat -- --num-threads 32 --time`.
  Use Cargo's default concurrency. Label vstd and every VeriFlat artifact
  independently hot/cold; a fully cached no-op is not a benchmark.
- Typecheck first, then verify the smallest function/module/package. Completed
  cross-crate work requires full workspace and 32-thread monolith checks.
- Treat >50 seconds as suspicious. Performance reports include Rust, VIR,
  verification, SMT, wall, and rlimit under identical cache/thread scope.
  Rlimit alone does not determine proof speed.
- Preserve the permanent build architecture and do not hand off new warnings.
- Before handoff run `git diff --check` and a style audit only on files changed
  in this session. Check bare/empty asserts, `assert forall`, loose reveals,
  assumes, dead ghosts, duplicate reveals, and new wrappers. Exclude pre-existing
  dirty files and the canonical `syscall_alloc_quota/` directory.
- The Codex hooks in `.codex/hooks.json` enforce a session-level two-pass
  reminder/gate for changed Rust files; they do not certify proof correctness.
