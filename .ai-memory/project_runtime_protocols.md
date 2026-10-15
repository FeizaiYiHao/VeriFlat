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

## Thread exit and zombie marks

- `syscall_thread_exit` is the only self-removal: enter (cpu → container →
  process → thread write locks; a served caller is woken with
  `ErrorIpcCalleeExited` onto shard `cpu_id` of the container's scheduler),
  one drop step per endpoint descriptor that holds an endpoint
  (`SyscallProgress::ThreadExit { next }`), for the process's last thread the
  reclaim steps, then finish (thread removed, quota absorbed by the process,
  cpu Idle on the default page table).
- Reclaim runs inside the same exit call: lock `PT(P)`, then under the root
  table detach every attached function `P` owns (emptying its IOTLB domain)
  and lock `IT(P)`; clear every user 4K leaf (present bit only), flush `P`'s
  PCID once on every cpu, unmap the cleared leaves and refund their pages,
  then clear, unmap, and refund every IOMMU 4K leaf (no IOTLB flush: no
  function translates through a write-locked IOMMU table), return all
  4K/2M/1G quota of the thread and process to the container
  (`ThreadExitReclaim`/`ThreadExitQuota`), unlock `IT(P)` and `PT(P)`
  (`ThreadExitZombie`). Finish of the last thread locks the container's PCID
  allocator (107) and releases `P`'s PCID, so a zombie's pcid+cr3 never
  enters any cpu's dirty bitmap. Table structure pages stay with the zombie.
- The thread's page goes back to the 4K allocator cache of the page's owning
  container through the authorized TCB `retype_thread_rwlock_to_4k_page_perm`
  (inverse of the thread mint); the owner's quota_4k grows by one.
- A zombie has no thread, no quota, no user or IOMMU 4K mapping, no attached
  function, and no PCID; it keeps its table structures and owns its PCI
  functions (U projects its
  `pagetable`/`iommu_table` as `None`). A zombie root process marks its
  container. Only the container-locking syscalls stutter `ErrorContainerZombie`;
  exit itself does not. Freeing the remaining structures is left to kill/reap.

- Kill invariant (`process_thread_wf`): a thread being killed belongs to a
  process being killed, and one writer holds both; killed thread and process
  lock ids sink to `(High, High, KILLED_LOCK_MAJOR, addr)`.

Primary code: `src/kernel/kernel_total_define_spec.rs`,
`src/kernel/implementation/syscall_thread_exit/`,
`src/kernel/implementation/allocate_free_4k_page/`,
`src/kernel/implementation/syscall_new_thread/`, and
`src/kernel/implementation/locker_unlocker/locker_unlocker_thread.rs`.
