//! Lock-order deadlock freedom over the kernel's own `KernelK` and `LocalContext`.
//!
//! # 1. What the theorems state
//!
//! `two_aligned_acquirers_with_ordered_wants_implies_no_wait_cycle` (two cpus),
//! `aligned_acquirers_with_ordered_wants_implies_no_wait_cycle` (a ring of any length, every edge a holder edge) and
//! `aligned_acquirers_with_holder_or_same_want_edges_implies_no_wait_cycle` (a ring whose edges are holder edges or
//! same-want edges, at least one a holder edge) state that cpus whose contexts are aligned with one kernel state cannot
//! wait on each other in a cycle. Their `requires` clauses and how each is discharged:
//! - `krnl.inv()`: **Verified**, every locker requires `old(self).inv()` and `kernel_step_boundary_raw` re-establishes it.
//! - `typed_lock_maps_aligned(krnl, lctx_i)` for every cpu: **Verified** per cpu by every locker, unlocker and
//!   `kernel_step_boundary_raw`; that all cpus align with the same `KernelK` at one instant is **TCB** (a).
//! - each cpu is in the Acquire phase: **Verified**, `wlock_requires` (`src/locks/lock_cell.rs:285`) and each locker
//!   require it (the deletion test shows the theorems do not use it).
//! - holder edge, `typed_lock_entry(obj) is Some` for the next cpu's wanted object: follows from alignment once the
//!   physical lock word is held, which is **TCB** (b).
//! - each wanted id is at most `kernel_obj_lock_id(krnl, obj)` (equal except for containers): **Argued** (a), with the
//!   one re-key residual listed there as open.
//! - `lock_id_acyclic(want)` for each cpu: **Verified** at every call site of a blocking primitive, **Argued** (b).
//! - same-want edge (a cpu waits behind a per-cpu reader-lock writer that has not taken every slot): **TCB** (b).
//!
//! # 2. TCB
//!
//! - (a) Step atomicity. At any instant every cpu's `LocalContext` aligns with the same `KernelK`: each top-level field of
//!   `KernelK` is touched only under its lock (the `&mut KernelK` aliasing argument), and the external_body
//!   `kernel_step_boundary_raw` (`src/kernel/kernel_k_define_spec.rs:288`) hands each cpu a state that satisfies `inv`,
//!   keeps its held objects (`kernel_step_boundary_framing`, :321) and stays aligned with its context.
//! - (b) The external_body lock words in `src/locks/lock_inner_t.rs` implement their contracts: a cpu holding the word
//!   has the typed entry, and a waiter spins only while another cpu holds it. This includes the per-cpu reader-lock
//!   writer (`wlock_unless_killed_with`, :200-232), which sets `SLOT_PENDING` and takes the slots one by one; the pending
//!   state is not in `KernelK`, so a cpu blocked behind it enters the theorem as a same-want edge. It also includes the
//!   per-cpu reader-lock reader that gives up on a mark (`rlock_unless_killed`, :288-317): it spins only while its own
//!   slot is busy, polls slot 0's kill mark while spinning, and returns as soon as it sees the mark.
//! - (c) The NMI handler (`boot/kernel/src/platform.rs:220`) serves every pending flush request, takes no lock, and NMIs
//!   arrive whatever the interrupt flag, so the flush waits at :134 and :152 end.
//! - (d) `ipi_remote_running_to_idle_raw` (`src/cpu/atomic_pcid_cr3.rs:73`): its contract requires the target outside a
//!   kernel step (`!(cpu_op[cpu_id] is InStep)`, so its interrupt flag is set) with its cpu lock marked; the target takes
//!   the IPI and acknowledges in its idle loop (`platform.rs:212`).
//! - (e) The IOMMU completes every queued invalidation, so the holder of `INVALIDATION_LOCK`
//!   (`boot/kernel/src/iommu.rs:275`), a leaf lock outside `LocalContext` whose holder only polls hardware, releases it.
//! - (f) Interrupts are delivered: the maskable IPIs of (d) and the wake IPI of `ipi_wake` (`src/cpu/cpu_ipi.rs:15`) reach
//!   their targets.
//!
//! # 3. Argued
//!
//! - (a) A spinning cpu's wanted id stays the K id. The locker computes the id from the current `KernelK` in the step that
//!   starts the spin (`lock_id_acyclic(k.<family>.lock_id_by_*(obj))`, the locker per family is in `lock_order.rs`), and
//!   the waiter reaches the object only through objects it holds or their read-only owner data, which the step boundary
//!   keeps. A container waiter asks with `dynamic_container_lock_id` of its own owner and spins only while the holder's
//!   recorded owner is at or above it (`lock_inner_t.rs:164`), so its want is at most the K id. A victim thread of a
//!   killer whose state is unknown is ordered by depth: `wlock_kill_victim_thread`
//!   (`locker_unlocker_thread.rs:436`) requires the victim deeper than the killer's cpu (`killer_any_thread_lock_context`)
//!   and proves `lock_id_acyclic` from that before spinning, for every non-killed state of the victim.
//!   Re-keying: an id changes only by `update_lock_id` (`src/locks/local_context.rs:318`), in the Release phase, on an
//!   object the cpu write-holds. The theorems may be instantiated with each want set to the wanted object's current K
//!   id, so what a waiter needs is that every lock it holds stays below that id; a re-key that raises the id keeps this,
//!   and so does any re-key of an object whose locker proves `lock_id_acyclic` from depth for every state (killed-victim
//!   threads, `wlock_cpu` targets in a deeper container). Ids order owner first (Some below None), then the major.
//!   Raising or equal, no effect: thread RUNNING to SCHEDULED, blocked or idle, blocked or IPC_TRANSIT to SCHEDULED,
//!   rebalance moves (`syscall_schedule_switch_helpers.rs:267`, `syscall_ipc_endpoint.rs:583`, `rebalance_pull.rs:409`);
//!   cpu Running to Idle and Idle to Off (`syscall_cpu_offline_commit_helpers.rs:419`, :439); page owned to typed and
//!   typed to free or merged (`create_endpoint_from_staged_page.rs:121`, `unmap_4k_reclaim.rs:154`).
//!   Lowering, by transition:
//!   - thread endpoint-waiting to IPC_TRANSIT or RUNNING: no waiter at the old id; others reach the thread through its
//!     endpoint queue, whose lock the re-keyer holds, or as a kill victim (depth) (`syscall_ipc_endpoint.rs:339`,
//!     `syscall_ipc_call.rs:195`).
//!   - thread reply-waiting to RUNNING: no waiter at the old id; only its callee (the re-keyer's held running thread) or
//!     a dangling-chain reclaimer holding that callee killed reaches it (`syscall_ipc_call_reply.rs:177`).
//!   - thread SCHEDULED to RUNNING: no waiter at the old id; the re-keyer holds the scheduler shard that queues it, which
//!     a scheduler user or rebalance (holding every shard up to the victim's) must hold (`syscall_schedule_switch_helpers.rs:273`).
//!   - thread marked killed (to the minimal id): no edge, Argued (c) (`locker_unlocker_thread.rs:577`).
//!   - cpu Off to Idle: no waiter at the old id; `wlock_off_cpu` requires the cpu set write-held, which the re-keyer
//!     holds, `wlock_cpu` excludes Off, and `wlock_own_cpu` waiters hold nothing (`syscall_cpu_online.rs:107`).
//!   - cpu Running to Running at another process (`syscall_schedule_switch_helpers.rs:256`,
//!     `syscall_ipc_call_helpers.rs:178`): no re-key while a waiter spins; `wlock_cpu` has two callers: the kill_process
//!     one (`syscall_kill_process_victim.rs:340`) write-holds the marked victim thread running there, and a switch must
//!     re-key that thread under its lock; the kill_container one (`syscall_kill_container_cpus.rs:665`) takes an Idle
//!     target in a deeper container, ordered by depth for any state.
//!   - thread DANGLING (None, None, blocked) to KILLED (Some c, None) (`take_over_dangling_caller.rs:76`): no waiter at the
//!     old id; a dangling thread is reached only as the caller of its callee, which the re-keyer write-holds, and the
//!     chain reclaimer (`wlock_killed_chain_caller`) also needs that callee held.
//!   - `fresh_to_scheduled` (`process_subsystem_mutation.rs:971`, `thread_util_t.rs:667`): raises, RUNNING to SCHEDULED, on a
//!     thread born held by retype that no other cpu can know yet.
//!   - idle cpu moved to an ancestor container, (Some c, None) to (Some ancestor, None) (`syscall_kill_container_cpus.rs:795`):
//!     no waiter at the old id holding a lock; `wlock_own_cpu` waiters hold nothing, the kill_process `wlock_cpu` caller
//!     needs a running victim on the cpu, the kill_container one needs the cpu's owning set, which the re-keyer write-holds,
//!     and `wlock_off_cpu` needs Off.
//!   - page free to owned at allocator pops (`allocate_free_2m_page_pop_impl.rs:155`): no waiter at the old id; the popper
//!     holds the cache or pool list holding the page, and every free-page locker holds that list: pops, drains and refills
//!     (both lists), `merge_2m` (`freeze_merge_2m_sources` locks every 4K source list), `split_2m` (the 2M list) and
//!     kill_container drains and moves (the killed container's lists).
//!   - page last mapping, Mapped4k to Unavailable (`unmap_4k_remove.rs:93`, :190, `unmap_iommu_4k_remove.rs:87`,
//!     `unmap_2m_reclaim_in_window.rs:116`): no waiter at the old id, argued: `ref_count` counts CPU and IOMMU mappings
//!     (`src/page/page_def.rs:39`), so the removed entry is the only path; the re-keyer holds its table (write, or read plus
//!     the window write, or the IOMMU table), and every mapped-page locker holds a page-table, window or IOMMU-table lock.
//!     **Open**: that each such locker's held table is the one holding its page's entry is read from requires names,
//!     not checked caller by caller.
//! - (b) Every blocking primitive requires `lock_id_acyclic` of the id it spins on, so every call site proves it
//!   (Verified); `l2_entry_lock` (`src/pagetable_concurrent/l2_entry_lock_t.rs:14`) does not, and its caller
//!   `pagetable_concurrent_lock.rs:21` does; `wlock_kill_victim_thread` proves it in its own body. So do, for an
//!   unmarked object, `rlock_cpu_set_unless_killed` (`locker_unlocker_cpu_set.rs:289`, from its requires: every held
//!   cpu set is below the wanted one or marked, and no scheduler, needflush or allocator lock is held), which the orphan
//!   pull calls under its own cpu lock (`rebalance_pull_orphan.rs:150`), and `wlock_scheduled_thread_unless_killed`
//!   (`locker_unlocker_thread.rs:165`, :242), re-audited with its weaker requires: the cpu's process and thread lock maps
//!   are only subsets of its current process and thread, and cpu sets may be held; its body still proves the thread's id
//!   above every held one (callers `syscall_schedule_lock_helpers.rs:461`, `rebalance_pull.rs:504`,
//!   `rebalance_pull_orphan.rs:656`).
//! - (c) A marked (killed) object has id (High, High, `KILLED_LOCK_MAJOR`, minor) and killable waiters return as soon as
//!   they see `WORD_KILLED` or `SLOT_KILLED`, so they add no wait edge; `unkill` requires the Release phase and the
//!   killer unlocks in that same phase. Plain per-cpu reader-lock readers (`rlock`) do not check the mark, and their
//!   contracts require `lock_id_acyclic` against the marked (minimal) id. `rlock_unless_killed`
//!   (`has_kill_state_rlock_unless_killed`, `locked_points_to.rs:425`; wrapper `rlock_cpu_set_unless_killed`) returns as
//!   soon as it sees the mark, so it adds no wait edge on a marked set and requires `lock_id_acyclic` only when the object
//!   is unmarked, like `wlock_unless_killed`; a reader stopped by a writer's pending bit is a same-want edge, as for plain
//!   readers.
//! - (d) Primitives that never wait add no edge: `downgrade` (`lock_inner_t.rs:331`), locks born held by retype, and
//!   `l2_entry_lock` of an unpublished L2 page (`pagetable_concurrent_impl_base.rs:224`).
//! - (e) A halting cpu holds no lock: `halt_until_ipi` (`src/cpu/cpu_ipi.rs:31`) requires `no_locks_held`, so no cpu waits
//!   on it.
//! - (f) From no wait cycle to no cpu waiting forever: every holder releases because every syscall finishes in finitely
//!   many steps; every exec loop and recursion carries `decreases` (repository rule), and the `liveness` crate gives the
//!   U-level step bounds per syscall. The spin locks are not fair, so no theorem states that a particular waiter
//!   eventually wins; that is out of scope.
#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_kernel_core::*;

pub mod lock_order;

pub use lock_order::*;

verus! {
global size_of usize == 8;
}
