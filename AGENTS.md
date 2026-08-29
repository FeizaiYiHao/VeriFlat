# VeriFlat Codex instructions

This file is the repository-level source of truth for Codex and every Codex
subagent.  Read it before editing.  `.clinerules` is for Cline and is not a
Codex steering file.  The documents under `.kiro/steering/` contain useful
background, but some architecture examples are stale; when they conflict with
this file or live code, this file and live code win.

## Scope and ownership

- Preserve the user's dirty worktree and unrelated edits.  Never reset or
  overwrite changes you did not make.
- A subagent edits only the files assigned by the parent.  It must report every
  changed file and verification run number.
- Freeze shared core APIs before parallel module verification.  Because all
  subagents use one worktree, do not run coupled migrations concurrently: one
  agent changing a common spec can invalidate every other agent's in-flight
  result.
- Shared-worktree diagnostics are visible immediately.  Do not leave temporary
  proof scaffolding in the tree when yielding or reporting completion.
- Before accepting a subagent result, the parent reviews the diff against this
  file; a green verification result is not sufficient.
- If a proof obligation exposes an unclear or apparently incorrect kernel
  invariant, ownership rule, or syscall semantic, report the exact mismatch to
  the user before changing the model.  Do not encode a guess or bend the proof
  around a semantically wrong invariant.
- If a proof exposes a fact missing from the existing invariant or producer
  contract, stop at that obligation and ask the user before changing the model.
  Do not substitute an ad hoc runtime recheck, data normalization, unrelated
  pre/postcondition, framing bridge, or alternate representation on your own.
- A direct postcondition that only exposes information the operation already
  guarantees may be added without asking.  Keep it semantic and narrow: do not
  turn a missing caller fact into a new precondition, model change, invariant
  change, or unrelated framing contract.
- An executable operation's preconditions must be limited to facts required by
  its own safety and semantics or by a direct callee.  Do not retain a
  precondition merely to prove an unrelated or removable postcondition.  A fact
  already implied by the operation's invariant or boundary state should
  normally be derived in an existing scoped entry proof rather than imposed on
  every caller.  Common examples are a current object being `Some`, map-domain
  membership, and a target not being held by the caller.  Do not force that
  migration when it creates a new proof stage or regresses same-scope
  verification: an exact safety/callee fact may remain as a measured
  normalization boundary.
- Operation postconditions must describe the result, exact mutation,
  permission/lock-ledger transition, invariant/phase/snapshot, stable public
  primitive semantics, or a fact consumed by a live caller.  Avoid broad
  field-by-field framing with no semantic or caller use.  A direct,
  non-quantified `old == new` framing postcondition is not a style violation by
  itself and need not be removed solely for terseness or a speculative SMT
  benefit; retain it when it keeps the producer contract explicit.
- Delete implementation, spec, and proof functions after confirming that they
  have no live caller or consumer.  A public syscall or an explicitly intended
  public kernel primitive is not dead merely because it currently has no
  in-tree caller.

## Current lock model

- `LocalContext` contains one held-lock ledger:
  `Set<(LockId, KernelObjId)>` (`Set<HeldLock>`).  Do not reintroduce typed lock
  maps, a parallel object set, or a scalar-only lock-id set.
- `lock_id_aligned(k, lctx)` is the exact object-sensitive mirror:

  ```text
  lctx.lock_id_set().contains((id, obj))
      <==>
  obj exists in its corresponding kernel map/array
      && the real object is read- or write-locked by lctx.thread_id()
      && id is that object's current dynamic lock id
  ```

- Acquisition requires directly that the target is not already locked by the
  current thread and inserts exactly `(current_id, obj)`. Unlock removes exactly
  `(current_id, obj)`. A dynamic-id change replaces the old pair with the new
  pair during the release-and-finish-syscall transition. Do not reintroduce a
  separate lock-entry freshness predicate; acyclicity already excludes the
  exact pair, while real target lock state is the operation's actual local
  precondition.
- A `Thread` always retains `owning_container`, `owning_proc`,
  `container_depth`, and `process_depth`; blocking does not erase ownership
  metadata.  Its dynamic lock id is state-dependent:
  - `RUNNING`: real container/process depths and `THREAD_LOCK_MAJOR`.
  - `SCHEDULED`: real container/process depths and
    `THREAD_SCHEDULED_LOCK_MAJOR`.
  - `SENDING`, `RECEIVING`, `CALLING`, `RECEIVING_CALL`, and
    `WAITING_REPLY`: `LockOwnerId::NotApp` for both owner components and
    `THREAD_BLOCKED_LOCK_MAJOR`.
- State transitions maintain dynamic ids forward: consume the old exact
  `(LockId, KernelObjId::Thread(ptr))` pair and produce the new exact pair in
  the transition/release contract.  Do not infer the old lock state backwards
  from `lock_id_aligned`.
- `NotApp` changes lock ordering only; it does not erase ownership or restrict
  IPC topology.  Ordinary send/receive rendezvous may cross container and
  process depths.  Do not add a same-depth or same-container restriction to
  ordinary IPC.
- `LocalContext` has no separate `wf()` predicate.  Its only ghost state is the
  thread id, phase, and held-lock ledger; consistency with kernel lock state is
  expressed exclusively by `lock_id_aligned` at the kernel layer.
- At `kernel_step_boundary`, the pair set is exactly unchanged, held-object
  state and rodata are explicitly framed, and final alignment is explicit.
- `all_objects_unlocked` means the thread holds neither a read nor a write lock
  on any kernel object, and is an externally tracked lock-state fact. Preserve it
  directly through operation contracts and boundary framing.  Do not derive it
  by expanding an empty pair set through global `lock_id_aligned`.

## Current syscall semantics

- `mmap_4k` currently keeps the deliberately blunt `quota == range * 4`
  precheck.  Establish VA-range cleanliness through the hierarchical page-table
  index-range predicates and their VA wrapper, not by looping over every 4K VA.
  Build page-table structure level by level, then install 4K leaves with kernel
  present and present set and `execute_disable == false`.  Do not revive the
  deleted/commented legacy mmap implementation.
- Ordinary IPC supports Empty and Pages payloads for `send` and `receive`.
  Pages IPC shares existing 4K data-page mappings and may allocate only missing
  receiver page-table directory pages; it never allocates data pages.
  `call`, `reply`, and other non-empty payload types remain out of scope.
- The endpoint queue direction is semantic invariant state:
  - `SEND` queues contain only `SENDING | CALLING` threads.
  - `RECEIVE` queues contain only `RECEIVING | RECEIVING_CALL` threads.
- An empty queue or a queue in the same direction blocks the current ordinary
  sender/receiver with its exact payload.  A blocked Pages payload must retain
  a well-formed `VaRange4K`.  For a non-empty opposite-direction queue, first
  call `wlock_thread_unless_killed(peer)`, then inspect the peer state and
  payload.
- The only successful rendezvous pairs are
  `(SENDING Empty, RECEIVING Empty)`, `(RECEIVING Empty, SENDING Empty)`,
  and the corresponding two arrival orders for equal-length Pages ranges.
  Pages rendezvous rejects the same process, a source hole, an occupied target,
  insufficient receiver quota, or an incompatible mapped-page owner before
  commit.  Page-table construction and leaf sharing begin only after every
  persistent check passes.  A killed peer returns `ErrorIpcPeerKilled`;
  payload/type, length, `CALLING`, `RECEIVING_CALL`, or any other
  incompatible combination returns `ErrorIpcTypeMismatch`.  On an error the
  peer stays queued, the current thread is not enqueued, and mappings and quota
  are unchanged.
- Endpoint queue length and reference count each use one `usize` field.  Keep
  the existing narrow trusted `< NUM_PAGES` bounds before increment; do not
  introduce a second ghost/typed counter or parallel accounting structure.

## Finished-proof acceptance rules

- Do not write a bare `assert(condition);`.
- Do not retain `assert(condition) by {}`.  If SMT proves the fact without a
  reveal or a genuinely necessary trigger bridge, delete the assertion.
- `assert(condition) by { reveal(opaque_predicate); }` is the normal accepted
  form.  Reveal only the predicates needed by that assertion.
- Do not retain `reveal(open_spec)` merely to make an open definition visible.
  Openness alone, however, does not prove that a scoped assertion is dead:
  nested invariant facts and `recommends` may still need that assertion as an
  explicit instantiation/normalization bridge.  Test deletion of the entire
  assertion.  If deletion fails and no narrower opaque producer is available,
  retain the scoped reveal form; never replace it with an empty `by {}`.
- Do not use function-scope/bare `reveal(...)` in an executable function or a
  multi-stage proof when a scoped `assert(...) by { reveal(...); }` can own it.
  A reveal must not pollute later proof obligations.  A single-stage `proof fn`
  may reveal directly when those reveals discharge only its declared ensures
  and there is no later sibling obligation to pollute.
- Do not introduce `assert forall`.  It leaks a quantified fact and its trigger
  into the remaining solver context.  Fix the producer's trigger or explicit
  postcondition instead.  The only exception is an already-established
  fold/linked-list proof pattern that the user has explicitly approved.  When
  auditing an existing unapproved `assert forall`, delete it and verify first.
  If its body supplied only necessary reveals, move only those reveals into the
  scoped assertion that consumes the fact; otherwise report the missing trigger
  or producer fact.
- The generic 4K effective-quota fold producers
  `lemma_{process,thread}_effective_quota_4k_fold_{sum_eq,change_by}_forall`
  in `allocator_quota_fold.rs` are an explicitly approved fold pattern.  Their
  quantified source/target-fold triggers are deliberate: keep their calls
  inside the scoped assertion that consumes the fold result, and do not replace
  them with an ownership-specific repository wrapper solely to eliminate the
  quantified producer.  This approval does not extend to wrappers that package
  an entire repository invariant or unrelated transition facts.
- The three 4K/2M/1G per-container conservation assertions inside
  `container_process_allocator_quota_wf_preserved_on_thread_add` are an
  explicitly approved transition-local fold closure.  Keep each quantified
  bridge inside the one scoped assertion rebuilding allocator-quota WF until
  the fold producers expose the corresponding post-state aggregate directly.
  This is not approval for unrelated operation-level `assert forall` bridges.
- Do not introduce proof-only ghost captures/snapshots.  An old dynamic lock id
  captured because a real transition changes that id is allowed only when its
  contract consumes the value.
- Do not make bare lemma calls that seed the surrounding SMT context.  Put a
  genuinely reusable narrow lemma inside the specific assertion that consumes
  it.  Never add a global wrapper lemma for one function or a lemma that merely
  packages an entire invariant proof.  A single-stage `proof fn` may directly
  call a narrower reusable lemma when that call directly discharges its declared
  ensures and does not seed any later proof obligation.
- The quantified lift inside
  `lemma_no_change_imply_memory_management_inv_for_page_fields_forall` is a
  measured exception to the proof-body `assert forall` ban.  It binds an
  arbitrary pre/post pair and delegates to the reusable leaf-preservation
  proof; directly revealing all memory-management leaves exceeds the
  kernel-core rlimit.  Keep the assertion local to that single-stage producer.
  This exception does not authorize new wrappers around other whole-kernel
  invariants.
- A missing generic algebra lemma over standard `Set`, `Seq`, or `Map` types may
  be added by following the repository's existing generic lemma patterns.  Ask
  the user before adding any new lemma specialized to a repository-defined type;
  first report the exact obligation and currently available ground facts.
- Do not add new no-change/framing lemmas.  Prefer explicit operation
  postconditions and direct field/object-state transmission.  Existing narrow,
  reusable lemmas may be used only when the live proof already establishes that
  pattern or the user approves it.
- Do not add `assume(...)`, `assume(false)`, or `#[verifier::external_body]` as a
  proof workaround without explicit user approval.  Temporary diagnostics must
  be removed immediately after measurement.
- Do not add `#[verifier::spinoff_prover]` unless the user asks for that exact
  experiment.
- Do not use blanket
  `broadcast use vstd::set::group_set_lemmas;`; it pollutes the solver
  context.  Activate only the narrow set lemmas needed by the consuming scoped
  proof.
- Do not change triggers on a kernel invariant or very common lemma without
  asking the user first, unless the current user request explicitly authorizes
  that exact trigger change.
- Do not add unnecessary proof.  Once verification is green, delete each new
  assert, reveal, lemma call, and ghost value one at a time and retain only what
  fails without it.  Establish a snapshot, ownership, or framing fact once
  before a region of pure reads; do not repeat it in each immediately following
  branch.  Branch-local closure remains appropriate after different state
  transitions.
- Current acceptance rules apply to every existing proof selected for cleanup
  or modification.  Age and a green verification result are not exemptions.
  Preserve an explicitly user-approved fold, linked-list, TCB, or measured
  prover exception unless the user asks to revisit it.

## Proof design

- Use `syscall_alloc_quota_4k` as the syscall-level reference for proof
  locality, control-flow clarity, and proof ownership.  Derive related entry
  facts together, keep lock/check/error control flow executable, and centralize
  mutation plus affected-invariant reconstruction when that materially
  simplifies the caller.  This is not a mandatory stage count, helper split, or
  requirement that every syscall have a commit helper.
- Prefer direct, explicit facts over chains such as
  `map key -> id set -> major bound -> fresh`.
- Prove local operation facts from direct preconditions, operation
  postconditions, or the invariant leaf that states that fact.  Do not run a
  global relation backwards to rediscover local state—for example, do not use
  `lock_id_aligned` or held-set membership to infer that a known object is
  `locked_by_thread` when the lock operation can state that fact directly.
- Proofs should remain structurally simple even when the property being proved
  is difficult.  If a local obligation needs a long chain through unrelated
  maps, ownership relations, lock ledgers, or wrapper invariants, treat that as
  a missing direct invariant conjunct or lower-level postcondition and improve
  the producer instead of preserving the indirect proof.
- Lower-level functions should expose frequently needed facts directly in
  postconditions: exact lock-set changes, target lock state, dynamic lock-id
  stability/change, and unchanged kernel fields.  Callers should not reopen
  implementation specs to rediscover these facts.
- For a single-key map mutation that already exposes `unchanged_except`, do
  not repeat map-wide quantified postconditions merely to frame fields on all
  entries.  State stable fields of the changed entry directly; other entries
  follow from `unchanged_except`.  If a live caller needs an element-wise
  consequence of the changed entry's sequence or map update, quantify only over
  that entry's elements and keep both pre- and post-state positive triggers.
  Retain an outer-map key quantifier only after a deletion experiment shows it
  is needed.
- Keep separate positive post- and pre-state `spec_index` triggers on
  `LockedMap::unchanged_except`, `UnLockedMap::unchanged_except`, and both
  array `*_unchanged_except` predicates.  Consumers instantiate these relations
  from either state independently.  A joint trigger is not equivalent: it
  requires both terms at once and breaks framing proofs.  Pre-only breaks
  kernel-core; family-wide post-only passes kernel-core but breaks the
  downstream new-thread proof.  Domain-membership/`index_valid` triggers are
  inconsistent across the family and produced no material wall/SMT/rlimit
  benefit.  Revisit only with paired focused and full-workspace measurements;
  never infer family robustness from a kernel-core-only green run.
- TODO(user-design): `LockedMap::unchanged_except` currently frames the
  exposed `RwLock` value but not the raw `PointsTo::lock_id()`.  Until the
  shared spec design is reviewed with the user, retain a narrow additional
  raw-lock-id postcondition where a live caller consumes it; do not infer that
  raw-id equality from `unchanged_except` or broaden the common spec locally.
- When a loop's caller consumes only an aggregate fold consequence of
  per-element results, maintain that aggregate over the processed prefix and
  expose the final scalar fold as a postcondition.  Do not export a quantified
  element-wise bridge solely to satisfy a fold lemma at the caller.
- For lock acyclicity, quantify directly over the held pair set and compare the
  `.0` lock-id component.
- Keep invariant reveals scoped and minimal.  Re-establish only invariant
  conjuncts whose actual inputs changed.
- Do not make a spec opaque merely because it groups existing narrower
  predicates.  A wrapper whose body is only a conjunction of named predicates
  should normally remain open, so callers do not need to reveal the wrapper
  merely to reach those existing leaves.  Retain opacity only when paired
  focused/full measurements show material SMT pollution, or when the wrapper
  is an intentional stable abstraction boundary.  When opening such a wrapper,
  remove its now-redundant reveals one at a time and remeasure.
- A syntactic conjunction wrapper may still be a necessary opaque boundary when
  opening it recursively exposes several open map-wide quantified leaves.
  Measure the recursive expansion, not only the wrapper body; in particular,
  do not classify a kernel-wide unlocked-except aggregator as cheap merely
  because each object-family predicate has a separate name.
- Treat map-wide quantified framing predicates, including
  `*_objects_unlocked_except` and quantified `*_unchanged` relations, as
  quantified producers rather than pure conjunction wrappers.  Keep them
  opaque by default and instantiate them with scoped reveals.  Test a
  representative predicate before any family-wide opacity change, and retain
  opacity when opening destabilizes an unrelated proof or materially increases
  SMT work.
- Treat `*_perms_wf` predicates that combine a map or array permission
  invariant with its object invariants as intentional high-frequency stable
  abstraction boundaries.  Keep them opaque and do not include them in generic
  conjunction-wrapper opening audits; opening them materially pollutes the
  global SMT environment and can destabilize unrelated proofs.
- Keeping an outer `*_perms_wf` wrapper opaque does not require its nested
  component predicates to be opaque.  Prefer a nested component open when it is
  primarily reached through the opaque outer boundary, because this removes
  redundant inner reveals without globally unfolding the wrapper.  Measure its
  independent direct consumers and retain inner opacity only for real pollution.
- For an opaque `wf` predicate with `recommends`, establish the recommended
  facts before consuming it and inspect which dependent opaque `wf` predicates
  the proof actually needs.  Reveal those dependencies inside the same scoped
  assertion; do not assume revealing only the outer `wf` is sufficient or
  reveal the dependency chain globally.
- Do not split a spec function, executable function, or proof lemma merely to
  create more verification units or prover parallelism.  If file size or
  scheduling requires a split, move intact functions into a small number of
  coherent modules; do not fragment equations.
- When several necessary `assert ... by` facts establish one transition stage,
  consolidate compatible facts into a single scoped proof block near the start
  of that stage only when focused and full measurements remain effectively
  flat.  Avoid scattering repeated reveals, but do not merge independently
  solvable ground assertions merely to reduce line count: a larger combined
  query can reduce prover parallelism and materially increase total SMT CPU.
- Preserve an established reveal order inside an expensive proof stage unless
  a paired measurement justifies changing it.  Reveal order can change AIR/SMT
  shape and rlimit even when the revealed set and logical meaning are identical;
  mechanical cleanup must restore both membership and order.
- Prefer an existing narrow no-change/WF-preservation lemma when it exactly
  matches the operation's producer contract.  If a legacy lemma is too broad or
  violates these rules, mark the callsite `TODO` and report it rather than
  copying the pattern into new proof.
- Do not hide a difficult callsite proof inside a new lemma.  If a proof cannot
  close using the intended reveals and existing narrow reusable lemmas, report
  the exact obligation and measured cost to the user.
- Remove a single-callee forwarding function when its body adds no executable
  behavior and its contract only repeats or weakens the callee contract.  Wire
  its sole caller to the real operation and delete result variants made
  unreachable by the real contract.  Preserve a wrapper that is an intended
  public primitive or a genuine semantic/crate boundary.

## Proof audit signals

- Repeated full-ledger extensionality proofs, repeated decomposition and
  reassembly of global framing predicates, a specialized proof helper with one
  textual consumer, and a pre-existing `#[verifier::spinoff_prover]` are audit
  signals, not automatic violations.  Do not reject a proof by macro name,
  helper call count, or predicate name alone.
- Remove a signaled proof item one at a time and run the smallest relevant
  verification.  If removal fails, classify the obligation before editing:
  retain a narrow proof for a genuine local mathematical fact; improve a
  producer/consumer contract when the proof only normalizes mismatched shapes;
  or preserve an explicitly approved reusable abstraction.  Evaluate removal
  of a prover annotation with both wall time and rlimit.
- An object-family-specific `*_objects_unlocked_except(..., exceptions)`
  contract is accepted exact framing when a caller cannot enumerate which
  objects of that family are held.  Do not classify it as a broad framing
  workaround merely because it summarizes a whole object family.
- When a consumer needs only such an object-family lock scope, prove that scope
  directly instead of first publishing an extensional equality for the entire
  held-lock ledger.  Exact ledger extensionality remains appropriate when the
  ledger itself is the operation result, such as the final empty set after all
  unlocks, or when paired measurements show that the scoped equality materially
  improves verification performance.
- A quantified operation postcondition that says every held object is
  unchanged, such as the held-object framing in `kernel_step_boundary`, is
  distinct from a proof-body `assert forall` and is accepted when it improves
  verification performance, or when it makes the contract or callers simpler
  without a measured performance regression.

## Build architecture

- Preserve the permanent dual build:
  - `src/lib.rs` is the monolithic Verus crate.
  - The Cargo-Verus workspace splits kernel core, page allocation, mapping,
    and syscall verification while compiling the same live implementation
    sources.
- The crate dependency layers are:

  ```text
  veriflat_kernel_core
  ├── veriflat_alloc_page
  │   ├── veriflat_syscall_new_thread
  │   └── veriflat_map_4k
  │       ├── veriflat_syscall_mmap_4k
  │       └── veriflat_syscall_ipc
  └── veriflat_syscall_alloc_quota
  ```

  Each child depends only on its ancestors.
  `new_thread` and `new_thread_with_endpoint` share the one new-thread crate.
  No syscall crate may depend on another syscall crate.
- `veriflat_kernel_core` owns defines, common utilities/lemmas, primitives,
  locks, `LocalContext`, linked lists, data structures/local proofs, `KernelU`,
  `KernelK`, kernel invariants/lemmas, locker-unlocker operations, and
  release-and-finish-syscall operations.  Page allocation and each syscall stay
  in their dedicated crates; syscall crates are terminal.
- Cargo package roots live beside the shared sources and use ordinary
  `pub mod ...;` resolution.  Do not reintroduce `#[path = ...]` wrapper
  roots or flat root-level syscall entry re-exports.  Terminal crate dependency
  imports stay private unless another crate genuinely consumes the item.
- Live syscall sources must not contain separate Cargo-versus-monolith
  `cfg` import paths.  The `split-crates` feature controls which
  implementation modules kernel-core compiles; it must not fork syscall source.
- Crate splitting is not a reason to invent bridge lemmas or re-prove an
  invariant differently.  If an existing spec, lemma, or helper is needed
  across a crate boundary, make the original item `pub`; if an `impl KernelK`
  method creates an unnecessary boundary, convert the original operation to a
  standalone function.  Keep only proof changes genuinely required by the
  crate boundary.

## Verification and performance

- In Windows-hosted Codex sessions, run repository build and verification
  commands inside WSL from `/home/xiangdc/VeriFlat`; do not use PowerShell as
  the build shell for the UNC worktree.
- Both verification wrappers record one monotonically increasing run number;
  include it in reports:
  - Focused/workspace: `./verify-workspace.sh --package <package>` and
    `./verify-workspace.sh`.
  - Monolith: `./verify.sh --num-threads 32 --time`.
- The Cargo-Verus pipelined multi-crate performance path is separate from both
  wrappers.  On the 32-logical-CPU reference machine, run:

  ```bash
  VERUS_PIPELINE_SMT=1 \
    verus/source/target-verus/release/cargo-verus verify \
      --workspace --exclude VeriFlat -- --num-threads 32 --time
  ```

  Keep Cargo's default concurrency for the reference measurement.  This must
  use the `verify` subcommand: `verify-workspace.sh` invokes `focus`, so setting
  `VERUS_PIPELINE_SMT=1` on that wrapper does not exercise the pipeline patch.
  See `patches/README.md` for reproducible cold-vstd and hot-vstd cache scopes.
- Every performance report must label vstd and VeriFlat crate artifacts
  independently as cold or hot.  A second fully cached Cargo run is a no-op,
  not a full verification benchmark.  Do not prewarm vstd through its standalone
  manifest when measuring VeriFlat; that Cargo fingerprint can differ from the
  workspace dependency build.
- Typecheck/compile before interpreting proof failures.  Then verify the
  smallest relevant function/module or Cargo package.  For a completed
  cross-crate change, run the workspace and the 32-thread monolith full build.
- Treat a verification taking more than roughly 50 seconds as suspicious and
  diagnose it rather than normalizing it.
- Use both wall time and rlimit when evaluating proof cost.  Rlimit alone does
  not establish that a proof is slow.  A small rlimit increase is acceptable
  when SMT and wall time remain effectively flat and the resulting proof is
  materially simpler or more readable; do not retain proof scaffolding solely
  to minimize rlimit.
- Performance reports include Rust, VIR, verification, SMT, wall, and rlimit.
  Compare runs only under the same Cargo cache/invalidation scope and thread
  configuration; identify cache-only/no-op workspace runs instead of reporting
  them as full benchmarks.
- Do not hand off a new compiler or Verus warning.  Investigate warnings such as
  ambiguous glob re-exports or unmet `recommends` rather than suppressing them.
- To localize cost, temporarily cut individual assertions or the postcondition
  with `assume(false)` only when the user has authorized that diagnostic, then
  restore the real proof immediately.
- To localize cumulative SMT cost inside one large verification bucket, place a
  temporary `assume(false)` at successive semantic stage boundaries and run the
  same focused command at each boundary. Treat each result as the cost of the
  prefix before that boundary; compare SMT time and rlimit under the same cache
  and thread scope. Keep only one cutoff at a time and remove it immediately
  after its measurement.
- To debug an opaque `xxx_wf` whose proof or `recommends` is unclear,
  temporarily assert its inline conjunction instead of the wrapper. Use
  Verus's unmet-`recommends` diagnostics to identify the dependent opaque facts
  and the minimal reveals that make those recommendations hold. Record
  generally required dependency reveals in `xxx_wf`'s own `recommends` path;
  do not leave the expanded diagnostic assertion in the finished proof.
- If an inline `xxx_wf` conjunction is still too large to diagnose, assert its
  conjuncts in small groups or one at a time to locate the first failing or
  expensive component. These partial assertions are diagnostic scaffolding:
  remove them after fixing the producer, trigger, or scoped reveal.
- Before handoff, run `git diff --check` and scan changed files for bare asserts,
  empty `by {}`, `assert forall`, loose reveals, `assume`, dead ghost snapshots,
  duplicate reveals, and newly added wrapper/framing lemmas.

## Layout

- Use the nearest live sibling as the formatting reference.
- Every syscall implementation lives under
  `src/kernel/implementation/syscall_xxx/`.  That directory's `mod.rs`
  contains declarations only: no implementation, specification, proof, or
  re-export code.
- `syscall_xxx/syscall_xxx.rs` contains only the syscall entry point(s).
  Put helper implementations, specifications, and proofs in sibling `.rs`
  files in the same directory.
- Keep submodule declarations in the directory's `mod.rs`.  Name split files
  with the original module prefix so repository search remains obvious (for
  example `locker_unlocker_pagetable.rs`).
- Avoid prose inside ordinary `proof {}` blocks.  Comments should explain a
  soundness boundary or non-obvious contract, not narrate each proof step.
