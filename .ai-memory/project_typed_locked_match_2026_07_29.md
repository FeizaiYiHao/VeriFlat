# Typed locked-match framing (2026-07-29)

## Design

- `container/process/thread/endpoint/scheduler/pagetable/page/cpu_locked_match_lctx`
  now take the relevant object collection, typed `Map<Key, LockId>`, and
  `LockThreadId`. `KernelK::locked_objects_match_lctx` supplies those arguments
  from `LocalContext`.
- The thread id is necessary for soundness: `Map<Key, LockId>` alone cannot
  distinguish this thread's lock from another thread holding an object with the
  same ordering id, and therefore cannot express the no-stealth-lock direction.
- `RwLock::{wlocked_by_thread,rlocked_by_thread,locked_by_thread}` provide the
  context-independent ownership projection used by those predicates.
- Allocator locked-match is split into
  `allocator_4k_locked_match_lctx`,
  `allocator_2m_locked_match_lctx`, and
  `allocator_1g_locked_match_lctx`, each paired with its typed allocator map.
  A 4k wrapper/callsite now reveals only the 4k predicate.
- Unchanged object collection + unchanged typed map + unchanged thread id now
  frame automatically. Aggregate callsite proofs in allocator, syscall quota,
  and syscall new-thread were narrowed to changed families only.

## Small proof repairs

- `allocate_free_4k_page` needed
  `reveal(allocator_4k_locked_match_lctx)` in the exact post-boundary
  all-caches-unlocked assertion.
- `LockedArray::view` is `closed`; the source contained a bridge comment but no
  bridge. Added trigger-free `LockedArray::lemma_view_index`, used only inside
  the fold-input assertion of `lemma_scan_fail_pool_nonempty`.
- Cache-pop free4k reconstruction dropped redundant
  `allocator_perms_wf`, `LinkedList::wf_perms`, and `LinkedList::wf_map`
  reveals and uses the smaller reveal set already used by the global-pop twin.
- No diagnostic `assume(false)` remains in
  `allocate_free_4k_page.rs`.

## Verification and timing

Counter reached **737**. Runs **697–737** are this continuation: 41 invocations
including deliberate failed/assume-false diagnostic comparisons.

- `kernel::kernel_k_define_spec`: 8 verified, 0 errors (#723).
- `kernel::implementation::syscall_new_thread`: 12 verified, 0 errors (#697).
- `kernel::implementation::syscall_alloc_quota`: all pass; timing #726:
  `syscall_alloc_quota_4k` 1.005s / 1.964M,
  `commit_alloc_quota_4k` 0.988s / 1.882M.
- `kernel::implementation::allocate_free_4k_page`: 12 verified, 0 errors
  (#722). Key SMT times:
  `allocate_free_4k_page` 2.221s / 3.246M,
  `alloc_4k_scan_all_caches_and_pool` 0.584s / 1.068M,
  `pop_stage_4k_page` 4.595s / 7.323M,
  `pop_stage_global_4k_page` 4.678s / 7.848M.
- New-thread timing #725: active top syscall is 0.343s; active merged create is
  0.230s; `add_new_thread_to_proc_container_and_scheduler` is 2.795s.
  The only >3s function is the unused legacy
  `create_thread_from_staged_page` at 4.320s / 5.833M.
- Locker/unlocker: 17 verified, 0 errors (#735).

## Measured remaining hotspots / decisions

- Both 4k pop functions spend their excess time in full
  `memory_management_inv` plus `process_management_inv` reconstruction. With
  the entire memory block admitted temporarily, the rest of cache-pop was
  2.329s / 3.967M. Individual ablations show the largest memory conjunct is
  `container_allocator_free_4k_page_wf`; quota-4k, allocator-pages, and the
  process-tree reconstruction are secondary. Irrelevant 2m/1g proof items
  together were only about 0.43M / 0.18s, so splitting the kernel invariant for
  that reason is not justified by current measurements.
- With Xiangdong's approval, both `container_scheduler_wf` forall triggers now
  use their antecedent domain membership:
  `container_map.dom().contains(c_ptr)` and
  `scheduler_map.dom().contains(s_ptr)`. This lets old/new domain equality
  instantiate both directions across a container lock-state-only update.
  `wunlock_container` then verifies at 0.587s / 1.038M in isolation.
- Full locker timing #735 exposed pre-existing wrapper hotspots:
  `wlock_page` 7.574s / 8.952M and
  `wunlock_page` 3.606s / 4.888M. Total locker SMT was 19.645s.
  Allocator and new-thread post-change rlimits were effectively unchanged from
  their pre-trigger baselines (#736/#737), so the new domain triggers did not
  cause a measurable cross-module rlimit regression.
