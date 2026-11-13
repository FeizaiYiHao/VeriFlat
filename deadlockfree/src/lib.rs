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
//!   re-keying case open.
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
//!   state is not in `KernelK`, so a cpu blocked behind it enters the theorem as a same-want edge.
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
//!   and proves `lock_id_acyclic` from that before spinning. **Open**: an id changes only by `update_lock_id`
//!   (`src/locks/local_context.rs:318`), in the Release phase, on an object the cpu write-holds; about 30 sites re-key
//!   pages (retype, reclaim), threads (schedule, IPC, reclaim) and cpus (online, offline, switch). A re-key that lowers
//!   the id while another cpu spins on the object at the old id would break the hypothesis; that no cpu can reach the
//!   object then (for example a free page reached only through the pool lock the re-keying cpu holds) is not checked
//!   site by site.
//! - (b) Every blocking primitive requires `lock_id_acyclic` of the id it spins on, so every call site proves it
//!   (Verified); `l2_entry_lock` (`src/locks/l2_entry_lock_t.rs:14`) does not, and its caller
//!   `pagetable_concurrent_lock.rs:21` does; `wlock_kill_victim_thread` proves it in its own body.
//! - (c) A marked (killed) object has id (High, High, `KILLED_LOCK_MAJOR`, minor) and killable waiters return as soon as
//!   they see `WORD_KILLED` or `SLOT_KILLED`, so they add no wait edge; `unkill` requires the Release phase and the
//!   killer unlocks in that same phase. Per-cpu reader-lock readers do not check the mark, but their contracts require
//!   `lock_id_acyclic` against the marked (minimal) id.
//! - (d) Primitives that never wait add no edge: `downgrade` (`lock_inner_t.rs:301`), locks born held by retype, and
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
