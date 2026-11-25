//! Liveness pilot over the kernel's user-visible step specifications.
//!
//! A behaviour is an infinite sequence of `Snap`s: the user state at each index with the label and cpu of the step taken
//! from it, consecutive states related by `labeled_step` of the noninterference crate, every state satisfying
//! `kernel_u_ownership_wf` as the noninterference trace theorems assume. The pilot covers `new_endpoint` (two steps),
//! `mmap_4k` (per-page loop with lock phases), and `alloc_quota_4k` (one step that can return
//! `ErrorContainerLockOrderConflict` while another cpu holds its container), and its behaviours take only steps of these
//! three syscalls. `pilot` holds the per-step facts both routes share; `route_explicit` proves the theorems with explicit
//! indices and fairness witnesses (IronFleet style), `temporal` is a small temporal logic, and `route_temporal` proves the
//! same theorems with it (Anvil style). Fairness and every environment assumption are explicit theorem hypotheses.
//! Round 2: `trace` adds `unmap_4k` and behaviours whose per-cpu invocations are prefixes of the traces the exec contracts
//! ensure, which bounds every invocation's own steps by its arguments; `contention` derives the lock invariants from a
//! quiescent start and proves waiters' progress under bounded contention.
//! Round 3: `pagetable_locks` proves pagetable and 2M window lock holder consistency inductive over traced steps from a
//! quiescent start. Round 4 adds that holders hold every window of their range, VA progress, and quota sufficiency,
//! so a cpu inside `unmap_4k`, or inside `mmap_4k` outside the fill phase, is never blocked.
//! Round 5: `world` is the closed world of every syscall covered so far, listed once in `world_label`, with one
//! `family_*` file per syscall family and the shared step frames in `frame`. It proves the two target properties for every
//! cpu inside a world syscall: never blocked, and a per-call bound on its own steps. The pilot and traced behaviours of
//! rounds 1 to 4 stay for their waiter theorems.
//! Round 6: `family_env` adds the trap, register, return-value, and TLB and context-cache fill events to the world. They
//! are not syscall steps, so they do not count toward a call's bound.
//! The kernel's four pending-write events (a user store issued or committed, a DMA request issued or completed) change no
//! U state (`kernel_k_*_implies_u_unchanged` in `src/kernel/kernel_step_wrappers/env_steps.rs`), so they have no label.
//! Round 7: `fill_quota` closes the fill phase of `mmap_4k`, so the world theorems no longer exclude it, and
//! `family_split_merge` adds `split_2m` and `merge_2m`.
//! Round 8: `family_kill` adds `kill_process` to the world without its five killed-thread reclaim steps, whose U specs do
//! not yet pin the reclaiming cpu (`kill_label` lists the rest, so adding them is one line). The kill invariants
//! (`kill_world_inv`: killers hold their walk, every marked process lies on its killer's walk, and well-formed threads,
//! cpus, and process tree, which the ownership facts leave out) start at the quiescent state and every world step keeps
//! them: `kill_frame` for the other families, `kill_steps` and `kill_own` for the kill's own steps. A killer whose
//! wanted locks are free has an enabled step (`kill_enabled`, `world_quiescent_behavior_implies_kill_never_blocked`). The
//! kill stays out of `in_world`: its trace spec bounds no length, so it has no per-call bound.
//! Round 9: `family_new_process` adds `new_process` and its two variants to the world. A cpu inside holds its thread,
//! the PCID allocator of its container until publish, and the child process after it (`new_process_locks_held`); as a
//! `table_sharer` it read-holds its process's page table and write-holds the windows of its range there and, once
//! published, the child's page table (`sharer_tables`). Its next step is always enabled, and a call takes at most
//! `4 * len + 3` steps.
//! Round 10: `family_exit` and `exit_own` add `thread_exit` to the world without its five killed-thread reclaim steps. An
//! exiting cpu holds its thread, process, and container (`exit_locks_held`, part of `world_inv`), and a process's last
//! thread reclaiming its tables is a `table_killer`. An exiting cpu whose wanted objects are free has an enabled step
//! (`world_quiescent_behavior_implies_exit_never_blocked`). Like the kill, the exit stays out of `in_world`: its trace
//! spec bounds no length.
//! Round 11: `family_offline` adds `cpu_offline_check`. Between its hold and its release or offline step the cpu is
//! write-locked without holding its running thread (`cpu_unbound`), so `cpus_wf` and `cpu_kept` keep only that thread's
//! empty progress there. The world restricts its steps by `world_allowed`, whose clauses are gaps of U (`u_gaps.md`).
//! `family_ipc` adds ordinary IPC (block and rendezvous, one step each) as the IPC representative.
//! Round 12: the release and fill-enter steps of mmap pin the thread to the acting cpu, so `offline_window_only` is gone;
//! publishing a process needs depth room, kept by `new_process_holds` from the restriction `new_process_depth_room`.
//! `bounds` states per-call step bounds of `syscall_thread_exit` and `syscall_kill_process`.
//! Round 14 (PCI functions per page table): the kill and the exit lock only the page table, then after the flush release the
//! process's PCI functions and write-lock its IOMMU table (`KillProcessUnownFunctions`, `ThreadExitUnown`), whose wanted lock is
//! that IOMMU table.
//! `pci_claim` joins the PCI family, a cpu inside `unmap_4k` has only RAM leaves left to clear, and `bounds` reads the step
//! bounds of the BAR map and unmap syscalls, which stay out of the world, from their trace specs.
//! Round 15: thread scheduling liveness. `run_queue` defines where a waiting thread stands (`waiting`, `shard_of`, `pos`),
//! the run-queue invariant `queue_inv`, and `waiting_step`, what one world step does to a waiting thread; `run_steps` proves
//! it for every world label. `run_measure` states part A without fairness: the run queues are FIFO, each head pop of a
//! waiting thread's shard lowers its position, a Schedule of the shard's cpu at the head runs it, and it changes shard
//! only from the head by a pull. `run_fair` states part B: under explicit fairness hypotheses a thread that is not
//! blocked eventually runs, or is killed or gone.
#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_kernel_core::*;
use veriflat_u_facts::*;
use veriflat_noninterference::{StepLabel, labeled_step};

pub mod behavior;
pub mod pilot;
pub mod route_explicit;
pub mod temporal;
pub mod route_temporal;
pub mod trace;
pub mod contention;
pub mod pagetable_locks;
pub mod fill_quota;
pub mod frame;
pub mod family_traced;
pub mod family_alloc;
pub mod family_new_thread;
pub mod family_cpu;
pub mod family_pci;
pub mod family_schedule;
pub mod family_env;
pub mod family_split_merge;
pub mod family_kill;
pub mod kill_enabled;
pub mod kill_frame;
pub mod kill_steps;
pub mod kill_own;
pub mod sharer_tables;
pub mod family_new_process;
pub mod family_exit;
pub mod exit_own;
pub mod family_offline;
pub mod family_ipc;
pub mod bounds;
pub mod world;
pub mod lock_order;
pub mod run_queue;
pub mod run_steps;
pub mod run_measure;
pub mod run_fair;

pub use behavior::*;
pub use pilot::*;

verus! {
global size_of usize == 8;
}
