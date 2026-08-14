# VeriFlat Codex handoff

Updated: 2026-08-13 after verification run #4319.

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

### Opaque PageTable leaf invariants

The old grouped predicates `levels_wf`, `disjoint_wf`, `mappings_wf`, and
`additional_wf`, together with all `reveal_page_table_*` broadcasts, have been
deleted. `PageTable::wf()` now directly lists its leaf predicates. The 14 leaf
predicates are opaque; `pcid_wf` deliberately remains open because it has no
quantifier trigger.

PageTable implementations now establish and consume leaf facts through scoped
`assert(...) by { reveal(...) }` blocks. Getter mapping facts are proved only at
the requested address prefix and immediately before returning. The enabled
base/destructive implementations contain no loose reveal or newly introduced
bare assertion. The mmap subtree remains disabled in
`kernel/implementation/mod.rs`.

Four pointwise resolver-unchanged helpers, four whole-state resolver-unchanged
helpers for L3/1G/L2/2M, and four narrow existence/uniqueness helpers replace
the old global `internal_resolve_disjoint` broadcast. Their requires clauses
contain only the backing state, path, or leaf facts actually used. Explicit
entry-field framing was added to `page_map_set_published` and
`page_map_set_published_in_map`, so callers do not reopen unrelated invariants
to rediscover writer post-state.

The expensive existing triggers were not changed. Profiling identified the
two-address triggers in `disjoint_l3` and `disjoint_l2` as the main source of
cross-product instantiation. Isolating them behind pointwise helpers reduced
`remove_l2_entry` from a 60M-rlimit diagnostic timeout to a passing proof around
7.15M rlimit; the accepted current proof remains below the default limit.

Current focused/module runs:

- #4311: `create_entry_l4`, 1.078s SMT / 2.358M rlimit;
- #4310: `create_entry_l3`, 1.123s SMT / 2.369M rlimit;
- #4298: `create_entry_l2`, 0.865s SMT / 1.806M rlimit;
- #4293: `map_4k_page`, 1.104s SMT / 2.750M rlimit;
- #4316: PageTable base module, 10/10, 4.673s SMT / 10.031M rlimit;
- #4299: `map_2m_page`, 1/1, 2.233s SMT / 5.156M rlimit;
- #4300: `remove_l2_entry`, 1/1, 1.326s SMT / 2.869M rlimit;
- #4301: `unmap_4k_page_user_view`, 2/2, 0.598s SMT / 1.344M rlimit;
- #4315: `unmap_4k_page_kernel`, 1/1, 0.650s SMT / 1.379M rlimit;
- #4317: destructive module, 7/7, 10.017s SMT / 16.328M rlimit;
- #4318: PageTable spec, 14/14;
- #4226: PageMap utility, 8/8.

`map_2m_page` profiling and cleanup used #4251/#4252 as the original focused
baseline (2.851s SMT / 7.305M rlimit). The accepted proof deletes the final
quantified bridge that merely repeated `wf_mapping_2m`'s domain/resolver
conjunct, and proves the L3 resolver framing with `resolve_l3_unchanged`, whose
single-final-state trigger is scoped to the framing assertion. The resulting
#4299 proof uses about 29.4% less rlimit and 21.7% less SMT time than #4251.
Profile #4280 still identifies `disjoint_l2` as the dominant quantifier (480
instances, cost product 2.093M); the L3 framing is much smaller (44 instances,
cost product 82k). Paired old/new triggers, broadcasting the pointwise helper,
and strengthening the common `disjoint_l2` trigger all regressed and were
restored.

The same whole-state pattern is now used wherever the corresponding backing
maps are genuinely unchanged: 1G framing in 2M map/L2 create/L2 remove, and
L2/2M/1G framing in 4K map and both 4K unmap paths. Target entries that really
change retain their target-excluding pointwise proofs. Compared with the prior
accepted modules, #4316 reduces base SMT time by about 27.8%, while #4317
reduces destructive SMT time by about 29.9% and rlimit by about 36.1%.

Full-tree verification initially exposed a solver-context-sensitive existing
postcondition in `syscall_new_thread_with_endpoint`. A final scoped assertion
now pairs the already-required `current_thread_ptr` entry equality with its
lock-id equality, giving `unchanged_except` the exact ground term it needs.
Deleting that assertion reproduces the failure; no runtime behavior or trigger
was changed.

### VA and page-pointer trigger isolation (2026-08-13)

The old trusted `va_lemma` has been deleted. Its quantified facts are now
separate ordinary proof functions, so each consuming assertion imports only
one quantifier. The old equality and inequality facts were intentionally
combined into `spec_index2va_injective`, with the paired new/old-address
trigger requested by the user. `map_2m_page` imports only this lemma inside
its `wf_mapping_2m` assertion; it has no active `assert forall`, broadcast, or
resolver-unchanged lemma.

The same isolation was applied where it closed directly:

- `map_4k_page` uses `spec_index2va_injective` only in its mapping-domain
  assertion and consumes ordinary whole-state 2M/1G unchanged lemmas directly
  in the two final mapping assertions;
- both 4K unmap paths use only `spec_index2va_injective` for 4K mapping
  framing; their redundant final VA-validity proof and 2M/1G unchanged calls
  were deleted;
- disabled mmap call sites now select either the 4K index-validity fact or the
  VA/index round-trip fact instead of importing the old bundle.

The old five-quantifier `page_ptr_lemma1` has likewise been deleted and split
into validity, pointer round-trip, index round-trip, pointer-to-index
injectivity, and index-to-pointer injectivity functions. All active call sites
now import only the required function inside their consuming assertion. The
unused three-quantifier `page_ptr_2m_lemma` was left alone because it has no
call sites and therefore does not seed solver context.

Latest focused results on the final source:

- #4468: `map_2m_page`, 1/1, 1.520s SMT / 4.162M rlimit;
- #4469: `map_4k_page`, 1/1, 3.468s SMT / 7.619M rlimit;
- #4470: `unmap_4k_page_user_view`, 2/2, 0.958s SMT / 2.430M rlimit;
- #4471: `unmap_4k_page_kernel`, 1/1, 0.943s SMT / 2.412M rlimit;
- #4464: `util::page_ptr_util_u`, 33/33;
- #4462: `page_pagetable_wf_eq`, 4/4;
- #4463: `pagetable_page_install_framing`, 6/6;
- #4465: whole-crate compile/typecheck passed.

The `pei_valid` mechanical migration initially made `PageMap::wf` quantify an
`int` and cast it to `usize`. This compiled but produced cast recommendations
and failed proof instantiation. Those four bounded quantifiers now quantify a
`usize` and cast only when indexing the sequence; #4467 verifies `pagemap`
7/7.

Full run #4466, taken before that PageMap correction, was not green: 582
functions verified and seven functions failed. The PageMap failure is now
fixed. The remaining failures are the existing/template-resistant
`wf_mapping_2m` reconstructions in `create_entry_l4`, `create_entry_l3`,
`create_entry_l2`, `remove_l2_entry`, and `remove_l3_entry`, plus several exit
leaf obligations in `remove_l4_entry`. Per the user's instruction, these were
not forced through the `map_2m_page` template. A post-fix full rerun has not
been performed. `git diff --check` passes, and `src` has no remaining call to
`va_lemma` or `page_ptr_lemma1`.

## Verification

Verification command:

```bash
./verify.sh --num-threads 32 --time
```

- current run #4319: 585/585; wall 29.285s, total SMT 106.583s, rlimit
  140,373,122;
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

### Final PageTable proof cleanup and performance (2026-08-14)

The post-trigger-adjustment cleanup is complete. Resolver/mapping reveals are
now scoped to the assertion that consumes them. In particular, the level
reveals used to prove create-entry resolver framing run before the mapping
invariant is revealed, and `remove_l2_entry` proves each of its three resolver
framing bridges in a separate scoped query. The latter change reduced the
function from 2.495s / 5.160M rlimit in the first cleanup regression to 1.460s /
3.878M rlimit.

Deleted proof surface:

- six zero-call resolver helpers: the L4/L3/L2 pointwise unchanged helpers,
  whole-state L3/1G/2M unchanged helpers;
- the unused page-index injectivity and bundled 2M page-pointer lemma;
- four zero-call VA validity/index lemmas;
- nine empty-map/domain assertions from `PageTable::new`, the redundant target
  resolver assertion in `map_2m_page`, and the redundant kernel-unmap mapping
  domain assertion;
- stale commented trigger alternatives and proof scaffolding.

The active resolver helper set is now only the six helpers with live scoped
consumers: `resolve_4k_l1_unchanged_at`, L3/L2 address uniqueness, direct L2
entry address uniqueness, L2 target existence, and whole-state L2 unchanged.
No invariant trigger was changed during this cleanup. `pcid_wf` remains open.

Final same-machine, single-thread, output-JSON runs:

- #4568 PageTable base: 10/10, 4.618s SMT / 10.262M rlimit;
- #4575 destructive: 6/6, 6.052s SMT / 15.542M rlimit;
- #4570 PageTable spec: 7/7, 0.258s SMT / 0.600M rlimit;
- #4571 PageMap utility: 8/8;
- #4572 page-pointer utility: 27/27.

The comparable 11 core PageTable functions total 10.594s SMT. The same-source
Z3 4.12.5 baseline (#3957) totaled 14.542s; the initial Z3 4.16 result (#3956)
totaled 44.045s. Current is therefore 27.1% faster than the old-solver baseline
and 75.9% faster than the initial upgraded-solver result. The only core function
still slower than the old-solver baseline is `map_4k_page` (1.494s versus
1.008s); every other core function is now faster.

Final full-tree run #4576: 576/576, wall 31.911s, total SMT 152.027s,
SMT-run rlimit 116,313,391. The lower verified-function count relative to old
runs is from deleting unused proof functions, not disabled executable modules.
The run prints only the existing automatic-trigger warnings in
`syscall_new_thread.rs` and `primitive/bitmap.rs`. `git diff --check` passes.
