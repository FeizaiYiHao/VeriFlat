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
  precondition merely to prove an unrelated or removable postcondition.
- Operation postconditions must describe the result, exact mutation,
  permission/lock-ledger transition, invariant/phase/snapshot, stable public
  primitive semantics, or a fact consumed by a live caller.  Remove redundant
  field-by-field framing and facts with no semantic or caller use.
- Delete implementation, spec, and proof functions after confirming that they
  have no live caller or consumer.  A public syscall or an explicitly intended
  public kernel primitive is not dead merely because it currently has no
  in-tree caller.

## Current lock model

- This experimental branch intentionally uses two independent held-lock
  representations in `LocalContext`:
  - `Set<(LockId, KernelObjId)>` (`Set<HeldLock>`) is the reverse ledger of
    every held kernel lock and its current dynamic ordering id.
  - One typed key set for each lockable object family is the forward ledger of
    which objects of that family are held.  Pages use `PageIndex`, CPUs use
    `CpuId`, allocator sets include `PageSize`, and the allocator-cache set also
    includes its cache `CpuId`.
- Do not add a direct equality, projection, or bridge invariant between the
  reverse ledger and the typed sets.  Each representation aligns independently
  with the real kernel lock state.
- `lock_id_aligned(k, lctx)` is the exact object-sensitive mirror:

  ```text
  lctx.lock_id_set().contains((id, obj))
      <==>
  obj exists in its corresponding kernel map/array
      && the real object is read- or write-locked by lctx.thread_id()
      && id is that object's current dynamic lock id
  ```

- Each typed-set alignment has the exact form
  `set.contains(key) <==> object exists && object locked_by_thread(lctx)`;
  map-backed families use map membership for existence, arrays use index
  validity, and allocator keys include the additional size/cache components
  needed to locate the physical lock.  Read and write ownership share the same
  typed set.
- For every acquisition, typed-set nonmembership is the caller-facing
  target-freshness fact: combine it with `typed_lock_sets_aligned` to establish
  that the real target is not already locked by the current thread.  The lock
  primitive retains that direct physical precondition, inserts exactly
  `(current_id, obj)` into the reverse ledger, and inserts exactly the typed
  object key into the corresponding forward set.  Unlock removes both exact
  entries.  A dynamic-id change replaces only the reverse-ledger pair; every
  typed set is unchanged.  Do not add a separate lock-entry freshness
  predicate.
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
- `LocalContext` has no separate `wf()` predicate.  Consistency with kernel
  lock state is expressed by `lock_id_aligned` for the reverse ledger and by
  `typed_lock_sets_aligned` for the forward sets.
- At `kernel_step_boundary`, both representations are exactly unchanged.  The
  forward typed sets determine the exact range of held objects whose state is
  framed; the reverse ledger is not used to enumerate that range.  Both final
  alignment predicates remain explicit.
- Replace `*_objects_unlocked_except` in the enabled experiment with direct
  typed-set equalities/subsets and exact set changes.  Express total absence of
  held locks as an empty reverse ledger.  Preserve independent object-state
  framing when it is semantically required.

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
- Open specs do not need `reveal`.  A reveal of an open spec is dead proof and
  must be removed.
- Do not use function-scope/bare `reveal(...)` when a scoped
  `assert(...) by { reveal(...); }` can own it.  A reveal must not pollute later
  proof obligations.
- Do not introduce `assert forall`.  It leaks a quantified fact and its trigger
  into the remaining solver context.  Fix the producer's trigger or explicit
  postcondition instead.  The only exception is an already-established
  fold/linked-list proof pattern that the user has explicitly approved.
- Do not introduce proof-only ghost captures/snapshots.  An old dynamic lock id
  captured because a real transition changes that id is allowed only when its
  contract consumes the value.
- Do not make bare lemma calls that seed the surrounding SMT context.  Put a
  genuinely reusable narrow lemma inside the specific assertion that consumes
  it.  Never add a global wrapper lemma for one function or a lemma that merely
  packages an entire invariant proof.
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
  fails without it.

## Proof design

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
- For lock acyclicity, quantify directly over the held pair set and compare the
  `.0` lock-id component.
- Keep invariant reveals scoped and minimal.  Re-establish only invariant
  conjuncts whose actual inputs changed.
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
  of that stage.  Avoid scattering repeated reveals across the implementation.
- Prefer an existing narrow no-change/WF-preservation lemma when it exactly
  matches the operation's producer contract.  If a legacy lemma is too broad or
  violates these rules, mark the callsite `TODO` and report it rather than
  copying the pattern into new proof.
- Do not hide a difficult callsite proof inside a new lemma.  If a proof cannot
  close using the intended reveals and existing narrow reusable lemmas, report
  the exact obligation and measured cost to the user.

## Build architecture

- This experimental branch intentionally narrows both builds to kernel core,
  4K page allocation, `syscall_alloc_quota`, `syscall_new_thread`, and
  `syscall_new_thread_with_endpoint`.  Mapping, mmap, IPC, and other syscall
  sources stay in the tree but are excluded from Cargo workspace membership and
  monolith module declarations while this lock-model experiment is measured.

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
  not establish that a proof is slow.
- Performance reports include Rust, VIR, verification, SMT, wall, and rlimit.
  Compare runs only under the same Cargo cache/invalidation scope and thread
  configuration; identify cache-only/no-op workspace runs instead of reporting
  them as full benchmarks.
- Do not hand off a new compiler or Verus warning.  Investigate warnings such as
  ambiguous glob re-exports or unmet `recommends` rather than suppressing them.
- To localize cost, temporarily cut individual assertions or the postcondition
  with `assume(false)` only when the user has authorized that diagnostic, then
  restore the real proof immediately.
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
