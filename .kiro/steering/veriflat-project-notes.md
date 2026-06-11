# VeriFlat — operational notes

Concrete things to remember when working on this codebase. Read
`Methodology.md` and `README.md` for the conceptual model.

## Project shape

- Microkernel verified with Verus, in `src/`.
- `verus/` is a submodule; the verifier binary lives at
  `verus/source/target-verus/release/verus`.
- Run `./verify.sh` from the project root to verify everything
  (`./verify.sh` works in both bash and zsh).
- `./activate` sources the Verus build environment.
- 295 verified, 0 errors is the current baseline (post-opaque refactor).

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
  - `memory_management/`, `process_management/`, `cpu_tlb_management/` —
    spec files, one bidirectional relation per file.
  - `implementation/` — verified syscall implementations.
- `src/lemma/`, `src/util/`, `src/primitive/`, `src/linkedlist/` — proof
  helpers and data structures.

## RwLock — five generic params

```rust
RwLock<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>
```

- `T` — the lock-protected payload. Always kernel-visible; user-visible
  iff `T::is_user_visible()`.
- `ROT` — read-only data. Same visibility as `T`. `borrow_rodata()` works
  without a lock.
- `KGhostT` — kernel-view-only ghost. Never user-visible.
  `update_kernel_ghost` mutates it without a lock; it's a kernel-view
  Release operation.
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

- `RwLock<…, NO_KILL_STATE>` exposes `wlock` (no kill check, would lock
  through a tombstone — but tombstones can't exist without
  `HAS_KILL_STATE`).
- `RwLock<…, HAS_KILL_STATE>` exposes `wlock_unless_killed` and
  `try_wlock_and_mark_kill`. Both fail if `killer_info.is_some()`.
- `wlock_external` / `wunlock_external` exist for TCB construction code;
  they have `requires true == false` to gate them. Use only inside the
  TCB.
- Renamed in the recent refactor: `try_wlock` → `wlock_unless_killed`,
  `try_rlock` → `rlock_unless_killed`. `try_wlock_and_mark_kill` kept
  the `try_` prefix.

## LocalContext

- Tracked ghost type minted by the TCB at syscall entry, threaded
  through every kernel call by ownership.
- Two phase states: `kernel_view_locking_state` (per atomic section,
  `Acquire → Release`) and `user_view_locking_state` (per syscall,
  same shape).
- `lock_seq: Seq<LockId>` — strictly ascending under `LockId::spec_gt`,
  enforcing global lock ordering.
- `unlock_requires<T>(...)` says: `T::is_user_visible() ==>
  user_view_locking_state is Release`. Wired into both `wunlock`
  variants. The user-view linearization point is mandatory before any
  user-visible lock can be released.

## Spec-design idioms

### Opaque spec functions (replaces the old `_proof`/`_inner` triple)

```rust
#[verifier::opaque]
pub open spec fn FOO_wf(...) -> bool { /* body */ }
```

To unfold inside a proof block: `reveal(FOO_wf);`.

When an exec/proof function needs many specs unfolded, put them all in
one `proof { reveal(...); reveal(...); }` at the top of the function
body. Reveals stay in scope for the whole function.

### Bi-directional relation pattern

For X ↔ Y:

```rust
#[verifier::opaque]
pub open spec fn x_y_wf(x_map, y_map) -> bool {
    forall|x_ptr| x_map.contains(x_ptr) ==>
        /* x's forward refs are in y_map.dom() */
    forall|x_ptr, y_ptr| where x.refs_y(y_ptr) ==>
        /* derived field consistency, e.g. y.parent == x_ptr */
    forall|y_ptr| y_map.contains(y_ptr) ==>
        /* y's back refs are in x_map.dom() */
}
```

Each clause needs `#![trigger ...]`. Trigger on the actual lookup chain
that appears in the formula.

### Page state with ghost payload

`PageState` derives `Clone, Copy, Debug, PartialEq`. Adding a variant
with `Ghost<T>` payload breaks the derives. The pattern is to put the
payload as a regular type (e.g., `RwLockThreadPtr` which is `usize`)
and treat it as ghost-only at the use site. Match with
`state is OwnedXk && state->OwnedXk_thread_ptr == ...` because
`matches PageState::OwnedXk{thread_ptr}` doesn't compose with `==>`.

## Tools available

- `./verify.sh [args]` — runs Verus on the whole crate. Pass
  `--verify-function FOO` to focus.
- `mcp_verus_mcp_server_verify_all` — verify whole crate or a module.
- `mcp_verus_mcp_server_verify_and_diagnose` — verify a single function
  with a prescriptive `nextAction`.
- `mcp_verus_mcp_server_search_vstd_lemmas` — search standard library.
- `mcp_verus_mcp_server_read_verus_guide` — read Verus docs.

The MCP tools are auto-wired in `.kiro/settings/mcp.json`. They run on
macOS via `./verus.sh`.

## Conventions to follow

- **No `_inner`/`_proof` triples in new code.** Use `#[verifier::opaque]`
  + `reveal(...)`.
- **Bi-directional specs are opaque.** Top-level conjunctions like
  `container_tree_wf` are plain `pub open spec` and just AND the parts.
- **`LockMinorTrait` for objects in collections is provided by the
  wrapper** (`PointsTo::lock_minor() == addr` for `LockedMap`,
  `LockedArrayElement::lock_minor() == index` for `LockedArray`).
  Inner objects don't need their own minor field. Exception: objects in
  bare `RwLock`s (e.g., `AllocatorQuota`, `LinkedList`) carry their own
  `Ghost<LockMinorId>`.
- **Triggers spell out the full chain.** `#![trigger
  m.spec_index(k).view().some_field]`, not auto.
- **Match arms with `matches` + `==>`** need parens or use the
  `is`/`->` accessor pattern.

## Running things

- Verify: `./verify.sh`
- Verify single function: `./verify.sh --verify-function name --verify-module path::to::module`
- Activate Verus build env: `source activate`

## Common gotchas

- `Ghost<usize>` doesn't impl `Clone, Copy, Debug, PartialEq`. Don't put
  it in `derive`d enums/structs. Use the underlying type and treat it as
  ghost at the use site.
- macOS sed needs `-E` for extended regex and doesn't support `\b` word
  boundaries. Use punctuation boundaries (`(`, `<`, `,`, etc.) instead.
- Reveal scope is the proof block, not the file. For exec functions
  needing many reveals, batch them at the top.
- `cpu_tlb.rs` (in `kernel/`) and `pagetable_tlb_spec.rs` (in
  `memory_management/`) are NOT in the module tree. Don't bother fixing
  errors there — they're stale.
- `container_tree_check_is_ancestor` and `process_tree_check_is_ancestor`
  are exec functions that need 6 reveals each. The pattern is
  `proof { reveal(a); reveal(b); ... }` at the top.

## Recent state (as of this writing)

- 295 verified, 0 errors.
- All `_wf_proof`/`_wf_inner`/`closed` triples have been refactored to
  `#[verifier::opaque] pub open spec fn`.
- `RwLock` was just split from 4 generic params (`T, ROT, GhostT,
  HAS_KILL_STATE`) to 5 (added `UGhostT`).
- Pages got an `Owned4k{thread_ptr}` / `Owned2m` / `Owned1g` variant
  with bi-directional spec in `pages_owned_spec.rs`.
- The kill-protocol's `try_wlock_and_mark_kill` has a verified outer
  wrapper but the retype-from-object trusted primitive isn't written
  yet.
- `unlock_requires` is now wired into both `wunlock` impls.

## User-view linearization & the KernelSteps ledger (session learnings)

This is the model for proving syscalls are user-visibly atomic. Read
`Methodology.md` for the "why"; this is the operational "how".

### The pieces

- `KernelU` (`src/kernel/kernel_u_define_spec.rs`) — the user-visible
  projection of kernel state. `kernel_k_to_kernel_u(k: KernelK) -> KernelU`
  is `pub open spec` (auto-unfolds). It reads ONLY:
  - `k.cpu_array.view()[i].view()` (per-cpu payload: owning_container,
    state, current_process, current_thread), for `i in 0..view().len()`, and
  - `k.process_map` views + `k.get_process_pagetable(ptr)` (which reads
    `process_map` + `pagetable_map`).
  It does NOT read container_map, allocator maps, or any lock state. So any
  operation that preserves cpu payload views + process_map + pagetable_map
  leaves the projection unchanged.
- `KernelStep` / `KernelSteps` (`src/kernel/kernel_total_define_spec.rs`) —
  a tracked ledger threaded through a syscall. Each step records
  `old_u/old_k` (at the linearization point) and `new_u/new_k` (at section
  end).
- `begin_user_view_step(&mut self, kernel_k: &KernelK, lctx: &mut ...)` —
  trusted `proof fn`. Appends a step capturing current state (new_* ==
  old_* placeholder). Requires kernel-view + user-view BOTH `Acquire`;
  flips BOTH to `Release` (no more locks may be acquired; user-visible locks
  may now be released). This is the linearization point.
- `end_user_view_step(...)` — trusted `proof fn`. Overwrites the open
  step's `new_*` with current state. Requires user-view `Release` +
  non-empty ledger; flips user-view back to `Acquire`. Kernel-view phase
  unchanged.

### Design rule (from the user)

When a user-view step BEGINS, no more locks may be acquired (kernel-view is
now Release). So the section between begin and end may only RELEASE locks.

### inv() is lock-state-independent

`KernelK::inv()` depends on object VIEWS, not `locking_thread`. So locking or
unlocking an object preserves `inv()` — but Verus still invalidates facts
about the changed field, so you must RE-ESTABLISH inv() after any
lock/unlock (the big `reveal`-laden proof block; see
`release_all_and_finish`). That block is the canonical template: copy it and
adapt `self`/`old(self)`.

### KernelK fields (for framing arguments)

`pagetable_map, page_array, cpu_array, cpu_tlb, root_container,
container_map, scheduler_map, process_map, thread_map, endpoint_map,
allocator_4k_map, allocator_2m_map, allocator_1g_map, default_pagetable`.
A call on `self.<field>` frames all the OTHER fields (struct equality
preserved automatically) — use this to argue most inv() conjuncts are
unchanged.

### Lock-op spec facts worth remembering

- `LockedMap::wlock_unless_killed` (`src/locks/locked_map.rs`): UNCONDITIONAL
  ensures preserve BOTH lctx phases (`kernel_view_locking_state` and
  `user_view_locking_state` unchanged) and give `unchanged_except(old, key)`.
  The FALSE (killed) branch additionally gives `old[key] == final[key]` and
  `final.lock_map() == old.lock_map()` — i.e. the map is fully restored, so
  the call is a complete no-op on `self`.
- `wunlock_ensures` (rwlock.rs): `new.locking_thread() is None`, `new.inv()`,
  `new@ == old@`, rodata/ghosts preserved. So a wunlock preserves the
  payload view.
- `cpu_array` is `LockedArray<Cpu, …, NUM_CPUS, CPU_HAS_KILL_STATE>` and is
  unlocked with the plain `wlock`/`wunlock` (NO_KILL API), so
  `CPU_HAS_KILL_STATE` behaves as no-kill here; cpu `being_killed()` is
  always false.

## syscall_alloc_quota_4k — current status (IMPORTANT, half-finished)

File: `src/kernel/implementation/syscall_alloc_quota.rs`. Baseline is now
**384 verified, 0 errors** (was 295 → 382 → 384; the +2 are the two lemmas
below).

DONE and verified:
- `release_all_and_finish` — the factored quota-insufficient exit path
  (holds cpu+container+quota locks). Opens a user step, releases the 3 locks
  (quota→container→cpu), re-establishes `inv()`, closes the step. Carries the
  full no-op postcondition:
  `steps.len() > 0`, `last().new_k == final(self)`,
  `last().new_u == kernel_k_to_kernel_u(final(self))`,
  `last().old_u == last().new_u`. Takes steps as
  `Tracked(steps): Tracked<&mut KernelSteps>`.
- `lemma_view_len` (in `lock_array.rs`) and
  `lemma_release_preserves_user_view` (projection unchanged across the
  3-lock release) — supporting lemmas.
- The "success" TODO path is routed through `release_all_and_finish` for now
  (allocation not implemented; every outcome is currently a no-op
  `return false`).

NOT done (deliberately reverted to keep the crate green):
- The SYSCALL-LEVEL `ensures` (`!ret ==> <user step recorded, old_u==new_u,
  new_u==projection of final>`). It is achievable only once EVERY `return
  false` path records a step.
- The killed-container branch (`if let (false,_) = container_res`) still just
  `return false` (TODO). To finish it you must: prove `inv()` still holds
  (only cpu lock state changed since entry — container_map is fully restored
  by the failed wlock), then open/close a user step while releasing the cpu
  lock (a cpu-only analogue of `release_all_and_finish`).
- The blocker that stopped me: re-establishing `inv()` for the killed branch
  needs `container_cpu_wf` (a BIDIRECTIONAL container↔cpu invariant). Its
  REVERSE direction (cpu→owning-container) would not instantiate from an
  extracted lemma with view/element-equality preconditions, even with the
  trigger term present and the spec revealed+asserted. Recommended next
  approach: do the killed-branch inv re-establishment INLINE (so it sits in
  the same SMT context as the fresh `wlock`/`wunlock` ensures, where a plain
  `reveal(container_cpu_wf)` suffices — as it already does in
  `release_all_and_finish`), and tame the resulting query-size butterfly by
  extracting the OTHER, non-bidirectional conjuncts into lemmas instead.

The public signature of `syscall_alloc_quota_4k` was kept as the original
`tracked mut steps: Tracked<KernelSteps>` (by value) since, without the
syscall-level ensures, there's no need to change the public boundary.
