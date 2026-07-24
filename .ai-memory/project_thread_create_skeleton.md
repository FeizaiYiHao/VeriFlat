---
name: project_thread_create_skeleton
description: "Thread-creation skeleton landed (scheduler wrappers, retype TCB primitive, container-set proof fn, create wrapper) with 2 marked assumes to finish later"
metadata: 
  node_type: memory
  type: project
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

Thread-creation SKELETON landed 2026-07-18 (crate 466 verified, 0 errors). Built
bottom-up in `syscall_new_thread.rs` + `locker_unlocker.rs` + trait files.

**Prereq infra (was entirely missing — thread_map/scheduler_map were never
lockable):** added lock-trait impls: `LockOwnerIdTrait for ()` (ROT fallback →
NotApp) in lock_traits.rs; `Thread` got `LockOwnerIdTrait` (Some(container_depth)/
Some(process_depth)) + `LockUserVisibilityTrait`(false) + fixed its `lock_major_1`
to `THREAD_LOCK_MAJOR` (was wrongly PROCESS_LOCK_MAJOR); `Scheduler` got
`LockMajorTrait`(SCHEDULER_LOCK_MAJOR) + `LockOwnerIdTrait`(NotApp) +
`LockUserVisibilityTrait`(false).

**SPEC-GAP FIXED:** `scheduler_perms_wf` was defined but NEVER wired into `inv()`.
Added `self.scheduler_perms_wf()` to `subsystems_inv()` (kernel_k_define_spec.rs).
Only ripple: `wlock_container_unless_killed` needed one added
`assert(self.scheduler_perms_wf());` before its subsystems_inv assert.

**wlock_scheduler / wunlock_scheduler** (locker_unlocker.rs): NO_KILL LockedMap
wrappers mirroring wlock_page/wunlock_page; carry locked_objects_match_lctx;
memory_management_inv holds with a bare `assert(self.memory_management_inv())`
(scheduler_map absent from every memory conjunct). VERIFIED, no assume.

**retype_staged_page_to_thread** (external_body TCB, syscall_new_thread.rs):
Owned4k{process}→Allocated4k{AsThread} + UNSTAGE from temp_alloc_cache_4k +
quota_4k−1 (so process_effective_quota_4k UNCHANGED) + thread_map grows at
key=page_ptr, write-locked. Does NOT ensure inv() (thread not yet wired). Body
unimplemented!() (TCB idiom).

**container_thread_wf_preserved_on_thread_add** (proof fn) + `container_map_gained_thread`
(spec): re-establish container_thread_wf after adding thread to direct
owned_threads + each ancestor's owned_indirect_threads. **Body is `assume` —
DEFERRED** (provable by 4-quantifier case split on t==t_ptr / uppers.contains(c)).

**create_thread_from_staged_page** (spinoff_prover, NOT external_body): LIVE
retype call (preconditions genuinely discharged) → then DEFERRED wiring
(scheduler push_tail, owned_threads push_tail, container-set inserts) + inv()
rebuild. 3 post-retype facts proven by `assert` (thread in map / wlocked / perm
id); only `assume(self.inv())` deferred.

**2 assumes left to finish (both provable, NOT assume(false)):**
1. `syscall_new_thread.rs:~360` `assume(self.inv())` in create wrapper — needs the
   3-step wiring done first, THEN the fold-insert-of-zero conservation axiom +
   process_thread_wf/container_thread_scheduler_wf rebuild.
2. `syscall_new_thread.rs:~567` `assume(container_thread_wf(...))` in the container
   proof fn — the 4-quantifier membership case split.
Plus the still-needed **fold-insert-of-zero axiom** (kernel_fold_axioms.rs) for the
conservation law when a zero-pending-quota thread joins owned_threads/owned_indirect_threads.

Next: wire the container-chain + scheduler LOCKING into syscall_new_thread's
quota-sufficient path (currently locks only cpu+process), then discharge the 2
assumes. See [[project_syscall_new_thread]], [[project_lockedmap_insert_tcb]].

**UPDATE 2026-07-18b:** (1) Made `scheduler_perms_wf` OPAQUE (matches every other
`*_perms_wf`); added `reveal(KernelK::scheduler_perms_wf)` beside the 19
`reveal(KernelK::default_pagetable_wf)` subsystems_inv sites + in both scheduler
wrappers' top proof blocks (needed BEFORE the scheduler_map.wlock/wunlock call for
its perms_wf precondition). (2) WIRED the success path: `syscall_new_thread`'s
quota-sufficient branch now calls `commit_new_thread` (new `external_body`
orchestration helper: stage→retype→wire→unlock-all→close-step) and returns
`Success`. Extended the syscall ensures to admit `Success` with
`ret is Success ==> steps.last().old_u == kernel_k_to_kernel_u(*old(self))` (thread
create grows owned_threads = real user-view change); bridged commit's mid-syscall
`old_u` to entry via `kernel_no_change_to_user_view_fields_imply_kernel_u_eq`.
`container_ptr` for commit read from the PROCESS's rodata (not cpu's). Crate 466,
0 errors. 4 deferred markers remain: commit_new_thread + retype (external_body TCB),
create_thread `assume(inv())`, container proof-fn `assume`. Still need the
fold-insert-of-zero axiom.