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
