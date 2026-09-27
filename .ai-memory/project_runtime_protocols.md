---
name: project_runtime_protocols
description: Current user-view, staged-allocation, thread-creation, and unlock protocols
metadata:
  node_type: memory
  type: project
---

# Runtime protocols

## User-visible steps

- `KernelU` includes `LockStateU::{Unlocked, ReadLocked, WriteLocked}` on
  containers, processes, threads, endpoints, CPUs, and both ordinary and IOMMU
  page-table views. Modes come from the outer physical RwLock; owners and reader
  counts remain kernel-only. Allocator and other internal lock families are not
  projected.
- `KernelSteps` retains exact K and U snapshots and records complete U changes
  only at existing kernel boundaries and syscall finish. A mode-only change is
  a real step; acquiring and releasing within one section can still stutter.
- `kernel_u_nonlock_fields` resets only represented lock modes, including both
  nested page-table views. The derived `KernelSteps::nonlock_view` filters
  lock-only steps and normalizes the remaining transitions for syscall business
  contracts. Actual snapshots and recording never use this projection.
- Rebasing refreshes K only when the complete stored U still matches the current
  projection. Pending lock changes remain in the snapshot comparison. The strict
  stuttering wrapper requires nonlock fields and observable lock modes to agree.

## Staged page allocation and thread creation

- Temporary allocation caches belong to the allocating `Thread`, not to
  `Process`.
- `allocate_free_4k_page` stages the returned page as
  `Owned4k { thread_ptr }`, inserts it into that thread's
  `temp_alloc_cache_4k`, and returns the page still write-locked with its
  `LockPerm`.
- `create_thread_from_staged_page_merged` consumes the staged page, grows the
  thread map, wires the process/container/scheduler relations, and refreshes the
  held-lock pair when the page's dynamic lock id changes during Release.
- A thread may be unlocked only when both `free_quota_pending_clean()` and
  `temp_alloc_clean()` hold. Finish or roll back staged work before
  `wunlock_thread`; do not transfer the old process-level cleanup rule back to
  `wunlock_process`.

Primary code: `src/kernel/kernel_total_define_spec.rs`,
`src/kernel/implementation/allocate_free_4k_page/`,
`src/kernel/implementation/syscall_new_thread/`, and
`src/kernel/implementation/locker_unlocker/locker_unlocker_thread.rs`.
