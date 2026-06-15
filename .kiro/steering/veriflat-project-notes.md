# VeriFlat — operational notes

Concrete things to remember when working on this codebase. Read
`Methodology.md` and `README.md` for the conceptual model.

## Project shape

- Microkernel verified with Verus, in `src/`.
- `verus/` is a submodule; the verifier binary lives at
  `verus/source/target-verus/release/verus`.
- Run `./verify.sh` from project root to verify everything (works in
  both bash and zsh).
- `./activate` sources the Verus build environment.

**Current baseline: 402 verified, 0 errors.** Don't introduce regressions.

## Module layout

- `src/lib.rs` — crate root; re-exports everything.
- `src/locks/` — trusted base. `RwLock`, `LocalContext`, `LockedMap`,
  `LockedArray`, `PointsTo` glue. Mostly `external_body`.
- `src/define/` — types, constants, traits.
- `src/page/`, `src/proc/`, `src/cpu/`, `src/allocator/` — kernel object
  definitions (`Page`, `Container`, `Process`, `Thread`, `Endpoint`,
  `Scheduler`, `Cpu`, `PageAllocator`).
- `src/pagetable_seq/` — page table machinery.
- `src/kernel/` — global kernel state and invariants.
  - `kernel_k_define_spec.rs` — `KernelK` struct and the global `inv()`.
  - `kernel_u_define_spec.rs` — `KernelU` user-view projection.
  - `kernel_total_define_spec.rs` — `KernelStep`, `KernelSteps` ledger.
  - `spec_util.rs` — preservation lemmas, narrow trusted set-fold axioms.
  - `memory_management/`, `process_management/`, `cpu_tlb_management/` —
    spec files, one bidirectional relation per file.
  - `implementation/` — verified syscall implementations.
- `src/lemma/`, `src/util/`, `src/primitive/`, `src/linkedlist/` — proof
  helpers and data structures.

## RwLock — five generic params

```rust
RwLock<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>
```

- `T` — lock-protected payload. Always kernel-visible; user-visible iff
  `T::is_user_visible()`.
- `ROT` — read-only data. Same visibility as `T`. `borrow_rodata()` works
  without a lock.
- `KGhostT` — kernel-view-only ghost. Never user-visible.
  `update_kernel_ghost` mutates without a lock; kernel-view Release op.
- `UGhostT` — user-view-visible ghost. Same visibility as `T`.
  `update_user_ghost` mutates without a lock; kernel-view Release; if
  `T::is_user_visible()`, also requires user-view Release.
- `HAS_KILL_STATE` — `bool` const generic. Toggles whether the rwlock
  carries a `killer_info: Option<KillerInfo>` (kill-protocol marker).

Most concrete sites pass `(), (), ()` for ROT/KGhostT/UGhostT. Container,
process, thread, endpoint, scheduler, page-table all use
`HAS_KILL_STATE`. Page array, allocator's internal pieces use
`NO_KILL_STATE`.

## RwLock API split

- `RwLock<…, NO_KILL_STATE>` exposes `wlock` (no kill check).
- `RwLock<…, HAS_KILL_STATE>` exposes `wlock_unless_killed` and
  `try_wlock_and_mark_kill`. Both fail if `killer_info.is_some()`.
- `wlock_external` / `wunlock_external` exist for TCB construction code;
  gated by `requires false`. Use only inside the TCB.

## LocalContext

Tracked ghost type minted by the TCB at syscall entry, threaded through
every kernel call by ownership.

- `kernel_view_locking_state`: per atomic section (`Acquire → Release`).
  Acquire = locks may be taken. Release = no more acquires; releases
  only.
- `user_view_locking_state`: per user-step (`Acquire → Release`). Same
  shape. Flipped both directions by `begin/end_user_view_step`.
- `lock_seq: Seq<LockId>` — strictly ascending under `LockId::spec_gt`,
  enforcing global lock ordering for deadlock-freedom.
- `unlock_requires<T>(...)`: `T::is_user_visible() ==>
  user_view_locking_state is Release`. Wired into both `wunlock`
  variants. The user-view linearization point is mandatory before any
  user-visible lock can be released.

## KernelSteps + snap_shot discipline

`KernelSteps` is a tracked ledger threaded through a syscall, recording
user-visible atomic transitions:

```rust
pub tracked struct KernelSteps {
    pub ghost steps: Seq<KernelStep>,
    pub ghost snap_shot: KernelU,  // user-view at last refresh point
}
```

Each `KernelStep` has `old_u`, `old_k`, `new_u`, `new_k`. Steps are
opened by `begin_user_view_step` and closed by `end_user_view_step`.

The `snap_shot` field is the discipline mechanism that catches
unrecorded U-mutations:

- **Syscall entry** (precondition): `old(steps).snap_shot ==
  kernel_k_to_kernel_u(*old(self))`. Caller hands us a fresh snapshot.
- **`begin_user_view_step`**: snap_shot preserved.
- **`end_user_view_step`**: snap_shot refreshed to current projection
  (the user-step's mutations are now recorded in the ledger).
- **`kernel_step_boundary`**:
  - requires: `kernel_k_to_kernel_u(*self) == steps.snap_shot` (no
    unrecorded U-mutation).
  - ensures: snap_shot refreshed to post-interleaving projection.

If a syscall mutates U outside of a `begin/end_user_view_step` pair, the
snap_shot stays stale, and the next `kernel_step_boundary` will fail to
verify. This mechanically enforces "U-mutations only inside user-steps."

## Wrapper-per-lock-op convention (CRITICAL pattern for SMT cost)

Every lock primitive (`wlock_*`, `wunlock_*`, `wlock_*_unless_killed`)
gets a wrapper method on `KernelK` that internally calls the primitive
AND re-establishes `KernelK::inv()`. Each wrapper is
`#[verifier::spinoff_prover]`.

Live wrappers in `src/kernel/implementation/syscall_alloc_quota.rs`:

- `wlock_cpu`, `wunlock_cpu`
- `wlock_container_unless_killed`, `wunlock_container`
- `wlock_quota_4k`, `wunlock_quota_4k`
- `wlock_process_unless_killed`, `wunlock_process`

Consumer (syscall body) becomes a sequence of wrapper calls with NO
manual inv blocks between. Each wrapper carries its own SMT cost; the
consumer stays light. Adopt this pattern for every new lock primitive
introduced into the syscall layer.

## Per-invariant preservation lemmas

For each opaque bidirectional invariant, factor the heavy quantifier
reasoning into a dedicated lemma. Live in
`src/kernel/implementation/syscall_alloc_quota.rs` (private to the
module) and `src/kernel/spec_util.rs` (cross-module):

- `lemma_container_thread_wf_preserved` (4-quantifier reverse direction)
- `lemma_container_endpoint_wf_preserved`
- `lemma_container_scheduler_wf_preserved`
- `lemma_release_preserves_user_view` (kernel_k_to_kernel_u preserved
  across cpu-only release — local to the syscall file)
- `lemma_release_with_process_preserves_user_view` (TCB axiom in
  spec_util.rs — for per-process view-equality release paths)
- `lemma_process_tree_wf_preserved_for_tree_fields_eq` (in spec_util.rs)
- `lemma_container_process_allocator_quota_wf_preserved_for_*` (the two
  fold-spec preservation lemmas)

The pattern: each lemma takes a clean pre/post pair, requires what's
relevant (per-element equalities, dom equality, etc.), ensures the
specific wf-conjunct holds in post. Heavy reasoning is contained in
the lemma's own SMT query.

## Trusted set-fold axioms (`spec_util.rs`)

The fold-based conjunct of `KernelK::inv()` is
`container_process_allocator_quota_wf` — a forall over containers
asserting the per-container quota equation:

```
fold(owned_processes, sum + process_map[p].view().quota_4k)
  + fold(owned_threads, sum + thread_map[t].view().direct_cache_4k)
  + fold(owned_indirect_threads, sum + thread_map[t].view().indirect_cache_4k[depth])
  + allocator[c.allocator_ptr_4k].quota.view().value
  ==
  allocator[c.allocator_ptr_4k].total_free_pages.view()
```

Verus has no built-in extensional set-fold equality. To preserve this
across operations, four narrow `external_body` axioms in
`spec_util.rs`:

- `lemma_process_quota_4k_fold_eq_under_view_eq` (pointwise eq → fold eq)
- `lemma_process_quota_2m_fold_eq_under_view_eq` (same for 2m)
- `lemma_process_quota_1g_fold_eq_under_view_eq` (same for 1g)
- `lemma_process_quota_4k_fold_change_one` (one-element delta → fold delta)

Two verified preservation lemmas build on these (no longer
external_body):

- `lemma_container_process_allocator_quota_wf_preserved_for_quota_transfer`
- `lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op`

When adding new TCB axioms, follow this pattern: NARROW axioms (one
fact each, concrete maps, lambda body inlined verbatim), then VERIFY the
broad lemma on top.

## Spec-design idioms

### Opaque spec functions (replaces the old `_proof`/`_inner` triple)

```rust
#[verifier::opaque]
pub open spec fn FOO_wf(...) -> bool { /* body */ }
```

To unfold inside a proof block: `reveal(FOO_wf);`.

When an exec/proof function needs many specs unfolded, batch reveals at
the top of the function body in a single `proof { ... }` block. They
stay in scope. Re-issue inside nested `assert by { }` blocks.

### Bi-directional relation pattern

For X ↔ Y (mostly in `kernel/process_management/` and
`kernel/memory_management/`):

```rust
#[verifier::opaque]
pub open spec fn x_y_wf(x_map, y_map) -> bool {
    // forward refs from x to y
    forall|x_ptr| #![trigger ...]
        x_map.contains(x_ptr) ==> /* x's forward refs are in y_map.dom() */
    // derived field consistency
    forall|x_ptr, y_ptr| #![trigger ...]
        where x.refs_y(y_ptr) ==> /* y.parent == x_ptr, depth match, etc. */
    // back refs from y to x
    forall|y_ptr| #![trigger ...]
        y_map.contains(y_ptr) ==> /* y's back refs are in x_map.dom() */
}
```

Each clause needs `#![trigger ...]`. Trigger on the actual lookup chain
that appears in the formula.

### Page state with ghost payload

`PageState` derives `Clone, Copy, Debug, PartialEq`. Adding a variant
with `Ghost<T>` payload breaks the derives. The pattern: put the payload
as a regular type (e.g., `RwLockThreadPtr` which is `usize`) and treat
it as ghost-only at the use site. Match with:

```rust
state is OwnedXk
    ==> { let t = state->OwnedXk_thread_ptr; ... }
```

The `_thread_ptr` accessor is auto-generated by Verus from the variant.
Don't write `state matches PageState::OwnedXk{thread_ptr} ==> ...` —
`matches` doesn't compose with `==>`.

## Conventions to follow

- **No `_inner`/`_proof` triples in new code.** Use `#[verifier::opaque]`
  + `reveal(...)`.
- **Bi-directional specs are opaque.** Top-level conjunctions like
  `container_tree_wf` are plain `pub open spec` and just AND the parts.
- **`LockMinorTrait` for objects in collections is provided by the
  wrapper** (`PointsTo::lock_minor() == addr` for `LockedMap`,
  `LockedArrayElement::lock_minor() == index` for `LockedArray`). Inner
  objects don't need their own minor field. Exception: objects in bare
  `RwLock`s (e.g., `AllocatorQuota`, `LinkedList`) carry their own
  `Ghost<LockMinorId>`.
- **Triggers spell out the full chain.** `#![trigger
  m.spec_index(k).view().some_field]`, not auto.
- **`#[verifier::spinoff_prover]` on every helper, wrapper, lemma.**
- **Wrapper-per-lock-op for every new lock primitive added at the
  syscall layer.**
- **Narrow, concrete TCB axioms only.** No spec_fn-typed parameters in
  `external_body` axioms — Verus's higher-order matching is unreliable.

## Common gotchas

- `Ghost<usize>` doesn't impl `Clone, Copy, Debug, PartialEq`. Don't put
  it in `derive`d enums/structs. Use the underlying type and treat it as
  ghost at the use site.
- macOS sed needs `-E` for extended regex and doesn't support `\b` word
  boundaries. Use punctuation boundaries (`(`, `<`, `,`, etc.).
- Reveal scope is the proof block, not the file. For exec functions
  needing many reveals, batch them at the top.
- `cpu_tlb.rs` (in `kernel/`) and `pagetable_tlb_spec.rs` (in
  `memory_management/`) are NOT in the module tree. Don't bother fixing
  errors there — they're stale.
- `container_tree_check_is_ancestor` and `process_tree_check_is_ancestor`
  are exec functions that need 6 reveals each at the top of the body.

## Linearization model — quick reference

A syscall is one user-visible atomic transition. Lock acquisition order
is deadlock-free (`LockId::spec_gt`). The user-view linearization point
is `begin_user_view_step`; after it, no more locks may be acquired.

The model has TWO atomicity levels:
- **Kernel-view sections** (between `kernel_step_boundary` calls): one
  atomic transition each. Held objects pinned; unheld objects can change.
- **User-view steps** (between `begin_user_view_step` and
  `end_user_view_step`): one user-visible atomic transition each. May
  span multiple kernel sections, but our current syscalls don't.

The `KernelSteps.snap_shot` field enforces that U-mutations only happen
inside user-steps; the boundary's snapshot check catches stragglers.

## syscall_alloc_quota_4k — current state (REFERENCE EXAMPLE)

File: `src/kernel/implementation/syscall_alloc_quota.rs`. Fully
implemented including the success path. Reference for how to structure
syscalls in this codebase.

Path summary (all branches verified):
- container-killed → `release_cpu_and_finish` (1 lock held)
- quota-insufficient → `release_all_and_finish` (3 locks held)
- process-killed → `release_all_and_finish` (3 locks held)
- process-quota-overflow → `release_all_with_process_and_finish` (4
  locks held)
- all checks passed → `transfer_quota_4k_and_finish` (4 locks held;
  opens user step, mutates, releases, closes step, returns true)

Postconditions:
- failure: user step recorded, `old_u == new_u` (kernel-internal failure)
- success: user step recorded, `old_u == kernel_k_to_kernel_u(*old(self))`,
  `new_u` differs from `old_u` exactly by `process_map[p].quota_4k +=
  alloc_amount` (captured by the helper spec
  `kernel_u_only_process_quota_4k_changed`).

SMT timing reference (full call graph): ~1279 ms serial-summed across
~17 spinoff_prover queries. The syscall body itself: 124 ms. The
single-query monolith before factoring was ~5258 ms.

## Recent state (as of current writing)

- 402 verified, 0 errors.
- `syscall_alloc_quota_4k` fully implemented, all 5 exit paths verified,
  full pre/post including success-path delta.
- Wrapper-per-lock-op pattern in active use (8 wrappers).
- 4 narrow trusted set-fold axioms in `spec_util.rs`; 3 verified
  preservation lemmas + several other helper lemmas.
- `KernelSteps.snap_shot` field added; `kernel_step_boundary` enforces
  the snapshot discipline.
- `release_container_cpu_and_finish` exists but is currently unused
  (kept as a drop-in for any future flow).
