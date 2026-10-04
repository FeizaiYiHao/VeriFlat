//! Noninterference between two isolated container subtrees A and B over the kernel's user-visible
//! step specifications.
//!
//! Each syscall is a sequence of `KernelStep`s that may interleave with steps of other cpus, so
//! unwinding is per step: for every step specification, (1) a step taken by a thread of A leaves
//! B's `domain_view` unchanged (local respect), and (2) a step taken by a thread of A or B preserves
//! `isolated`. `trace_ni_at` composes them over a trace of steps of A and B; steps of cpus outside
//! both domains are not covered.
//!
//! Output consistency: the kernel pins each syscall's result to the user state at entry
//! (`*_syscall_result`, and `ipc_entry_result` for the IPC rejections), and each `*_oc` lemma shows
//! that result reads only the caller's `domain_view` plus the listed peer-side objects: whether the IPC
//! peer is killed for the entry rejection, and the peer thread with the handed-over cpu, its payload
//! endpoint or container, or its process and container for the rendezvous, endpoint transfer, and pages
//! check results. With `trace_ni_at`, steps of A between two states leave B's results unchanged.
//!
//! Not covered: object pointers and page addresses returned on success come from the shared global
//! allocator and are guaranteed only to be fresh, so which pointer or page a domain receives can
//! depend on allocations by other domains. This allocator channel is outside the proof.
#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_kernel_core::*;
use veriflat_u_facts::*;

pub mod domain;
pub mod isolation;
pub mod ni_alloc_quota;
pub mod ni_schedule;
pub mod ni_cpu_hotplug;
pub mod ni_new_thread;
pub mod ni_mmap_4k;
pub mod ni_unmap_4k;
pub mod ni_ipc;
pub mod ni_new_process;
pub mod ni_new_container;
pub mod ni_share_4k;
pub mod theorem;

pub use domain::*;
pub use isolation::*;
pub use theorem::*;

verus! {
global size_of usize == 8;
}
