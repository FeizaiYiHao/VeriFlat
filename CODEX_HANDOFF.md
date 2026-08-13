# VeriFlat Codex handoff

Updated: 2026-08-12 after verification run #3952.

## Read first

- `AGENTS.md` is the repository-level source of truth. Read it completely
  before editing.
- Preserve the dirty worktree. It contains substantial user work and prior
  migrations; do not reset, restore, or rewrite unrelated files.
- `src/kernel/implementation/mmap_4k` remains intentionally disabled in
  `src/kernel/implementation/mod.rs`. It was enabled only temporarily for the
  verification run listed below, then returned to its original disabled state.

## Completed refactors

### Allocator free-page ownership

The free-page variants now carry the allocator identity:

```text
Free4k { allocator_ptr: Ghost<RwLockPageAllocatorPtr>, state: ... }
Free2m { allocator_ptr: Ghost<RwLockPageAllocatorPtr>, state: ... }
Free1g { allocator_ptr: Ghost<RwLockPageAllocatorPtr>, state: ... }
```

The global-pool and per-CPU-cache directions are separate invariants, while
the public combined invariant is only their conjunction. Allocator/page
consistency is proved directly against the allocator's linked structures; it
no longer needs a `ContainerLockedMap` argument.

### Stable and dynamic held-lock ledgers

`LocalContext` contains two tracked sets:

- `lock_id_set`: only mutable-id objects;
- `stable_lock_id_set`: immutable-id objects.

`held_lock_id_set()` is their union for object-agnostic queries. Acquisition,
release, freshness, exact membership, allocator-lock exclusion, major bounds,
and acyclicity all dispatch through the object's lock-id mutability. Acyclicity
checks both ledgers.

`lock_id_aligned` is now exclusively the two-way kernel mirror for dynamic
Page and Cpu locks. Stable entries do not participate in it. Kernel boundaries
frame both ledgers exactly; the opaque `stable_object_lock_ids_unchanged`
contract exposes stable-id preservation only to the scoped assertions that
need it.

### RwLock type-level classification

The lock family now has a const type parameter:

```text
RwLock<T, ROT, KGhostT, UGhostT, const LOCK_ID_MUTABLE: bool,
       const HAS_KILL_STATE: bool>
```

The parameter propagates through `LockedMap`, `LockedArray`,
`LockedArrayElement`, and `locked_points_to`. `wlock`, `wlock_unless_killed`,
kill-mark acquisition, and every unlock path update the selected ledger.

Classification:

- mutable: Page, Cpu;
- stable: Container, Process, Thread, Endpoint, Scheduler, PageTable,
  IommuTable, PcidAllocator, allocator quota/cache/global-pool locks.

`LockPerm` now stores `ordering_lock_id`, the structured id used at acquisition.
Stable unlock removes that exact acquisition key instead of recomputing an id
from current object state. Dynamic unlock continues to use the current id, and
real dynamic-id transitions call `LocalContext::update_lock_id`.

### Migrated callers

All enabled locker/unlocker wrappers, allocator paths,
`syscall_alloc_quota`, `syscall_new_thread`, and
`syscall_new_thread_with_endpoint` use the split ledgers. The disabled
`mmap_4k` subtree was migrated as well: CPU/Page are dynamic;
Container/Process/Thread/PageTable are stable; PageTable writes explicitly
frame the stable ledger.

No temporary `assume` or diagnostic scaffold remains.

### Global-pool stage-pop lock ordering

`pop_stage_global_4k_page` now requires
`old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR)` instead of spelling
acyclicity against the current global-pool head. The predicate covers both
dynamic and stable held-lock ledgers. The function derives the head page's
ordering condition locally from its exact `Free4k { state: GlobalList, .. }`
state, and `scan_caches_and_alloc` no longer constructs the head-specific
`lock_id_acyclic` assertion before the call.

### Allocator and mmap proof cleanup

The allocator cleanup retained only changes with a verified neutral or positive
effect:

- deleted one duplicate
  `allocator_objects_unlocked_except_cache_pool` assertion in
  `alloc_4k_scan_all_caches_and_pool`;
- deleted a redundant `page.inv()` assertion immediately before the enclosing
  `page_array_wf` proof in `move_global_pool_head_to_cache_4k_one`;
- deleted an empty trailing `proof {}` in `syscall_mmap_4k`.

The redundant page assertion removal reduced
`move_global_pool_head_to_cache_4k_one` from about 2.669M to 2.517M rlimit on
the pre-upgrade verifier (about 5.7%). Experiments that moved the global-pool
head acyclicity proof into the callee, removed the stable-id reveal, combined
the two mmap range assertions, or removed the initial page-array fact all
increased cost or failed and were fully reverted.

Pre-upgrade final runs:

- #3926: enabled tree, 580/580; wall 26.511s, SMT 78.660s, rlimit 88,253,453;
- #3925: temporarily enabled mmap subtree, 21/21; SMT 9.136s, rlimit
  16,167,634.

### Verus upgrade and Z3-sensitive PageTable cleanup

The `verus` submodule was fast-forwarded from
`64c47f0043972a17bcb40cc893cfe3901068a15f` to the then-current official
`origin/main`, `a8751f2b81578a762b42d1fc5a96653601e7363c` (2026-08-12).
The built toolchain is now:

```text
Verus 0.2026.08.12.a8751f2
Rust 1.97.1
Z3 4.16.0
```

The release build completed and its vstd verification passed 2043/2043.

The first project full run on the new verifier (#3930) passed 578/580; Z3 4.16
made `create_entry_l4` and `remove_l4_entry` exceed the default 30M rlimit.
Diagnostics at raised rlimit measured about 79.6M/42s and 114M/47s,
respectively. The accepted cleanup:

- scopes PageTable `levels_wf`, `disjoint_wf`, `mappings_wf`, and
  `additional_wf` reveals to the assertions consuming them instead of
  broadcasting all invariant groups across the function;
- changes only `create_entry_l4`'s local all-empty input trigger from
  `spec_index(i).is_empty()` to `spec_index(i)`, so Z3 4.16 can instantiate it
  for field-level `wf_l3` obligations;
- proves the removed L3 page's `page_closure` equation directly from map
  domains and set membership;
- applies the same scoped-invariant cleanup to `map_4k_page`.

After cleanup:

- #3945: `create_entry_l4`, 1/1, about 5.706M rlimit and 2.511s SMT;
- #3944: `remove_l4_entry`, 1/1, about 2.096M rlimit and 0.876s SMT;
- #3950: `map_4k_page`, 1/1, about 4.192M rlimit and 1.790s SMT;
- #3951: temporarily enabled complete mmap subtree, 21/21;
- #3952: enabled tree, 580/580; wall 41.081s, SMT 182.740s, rlimit
  140,486,462.

The latest verifier is proof-correct but materially slower on this crate than
the previous Verus/Z3 pair. Do not compare rlimit values across Z3 4.12.5 and
4.16.0 as if they were the same unit; wall and SMT time also show the
regression. The final 32-thread hotspot report after #3952 was led by:

- `allocate_free_4k_page`: 12.756s;
- `LinkedList::remove_helper`: 11.046s;
- `pop_stage_4k_page`: 10.970s;
- `pop_stage_global_4k_page`: 10.674s;
- `create_entry_l4`: 8.694s;
- `alloc_4k_scan_all_caches_and_pool`: 8.554s;
- `remove_l2_entry`: 7.969s;
- `create_entry_l3`: 7.540s;
- `unmap_4k_page_user_view`: 6.995s.

## Verification

Verification command:

```bash
./verify.sh --num-threads 32 --time
```

- historical run #3888: 580 verified, 0 errors;
- wall 32.409s, estimated CPU 213.191s;
- total SMT 108.052s;
- rlimit 89,125,776.

Historical pre-upgrade verification after the global-pool stage-pop contract
simplification:

- run #3902: 580 verified, 0 errors.

Important focused runs:

- #3887: `kernel::implementation::allocate_free_4k_page`, 19/19, wall
  26.646s, SMT 17.173s, rlimit 16,575,623;
- #3885: `locks::rwlock`, 1/1, wall 18.267s;
- #3884: temporarily enabled complete `kernel::implementation::mmap_4k`,
  21/21, wall 23.888s, SMT 18.692s, rlimit 16,167,634;
- #3879: `mmap_4k_create_entry_install`, 2/2;
- #3876: `pagetable_seq::pagetable_impl_base`, 10/10;
- #3862: `kernel::implementation::syscall_alloc_quota`, 2/2;
- #3858: `syscall_new_thread_with_endpoint`, 3/3;
- #3855: allocator module before the final cleanup, 19/19;
- #3852: `syscall_new_thread`, 11/11.

`git diff --check` passes after the final whitespace cleanup. The full run still
prints existing low-confidence automatic-trigger notes in `primitive/bitmap.rs`
and two quantified expressions in `syscall_new_thread.rs`; they are warnings,
not verification failures.
