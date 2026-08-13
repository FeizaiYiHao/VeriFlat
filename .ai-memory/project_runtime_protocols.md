---
name: project_runtime_protocols
description: Current user-view, staged-allocation, thread-creation, and unlock protocols
metadata:
  node_type: memory
  type: project
---

# Runtime protocols

## User-visible steps

- Syscall semantic postconditions describe `KernelU` transitions, normally
  through an operation-specific `kernel_u_*_changed` predicate. They should not
  expose lock state, allocator caches, or other `KernelK` implementation detail.
- `KernelSteps` carries a `KernelU` snapshot and a sequence of user steps.
  `end_kernel_step` and `kernel_step_boundary` compare the final projection with
  that snapshot; kernel-only work is a stuttering step, while a changed
  projection appends a `KernelStep` and refreshes the snapshot.

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
`src/kernel/implementation/syscall_new_thread.rs`, and
`src/kernel/implementation/locker_unlocker/locker_unlocker_thread.rs`.
