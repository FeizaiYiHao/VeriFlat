//! Noninterference between pairwise isolated container subtrees over the kernel's user-visible step
//! specifications.
//!
//! Each syscall is a sequence of `KernelStep`s that may interleave with steps of other cpus, so
//! unwinding is per step: for every step specification, (1) a step taken by a thread of A leaves
//! B's `domain_view` unchanged (local respect), and (2) a step taken by a thread of A or B preserves
//! `isolated`. `trace_ni_at` composes them over a trace of steps of two domains A and B. Because
//! `isolated` depends only on the two domain views in well-formed states, a step of a third isolated domain keeps A and B
//! isolated (`third_domain_step_implies_isolated_preserved`), and
//! `pairwise_isolated_domains_trace_implies_isolated_and_view_unchanged` covers traces of any set of
//! pairwise isolated domains. The theorem is about direct interference, as in Atmosphere: the domains
//! of the set may each share endpoints and pages with a third party, such as a common server or an
//! ancestor container. Steps of that party, including an ancestor killing a domain, are not steps of
//! these traces, and that it does not relay between the domains is a property of its user program,
//! which enters here only as the honest-peer conditions of `trace_ni_at`.
//!
//! Output consistency: the kernel pins each syscall's result to the user state at entry
//! (`*_syscall_result`, and `ipc_entry_result` and `ipc_reply_entry_result` for the IPC rejections; mmap
//! returns the state it decided in, which on success is the state its first step starts from), and
//! each `*_oc` lemma shows that result reads only the caller's `domain_view` plus the listed peer-side
//! objects: whether the IPC peer or the recorded caller is killed for the entry rejections, the calling
//! head's payload for the acceptance result, and the peer thread with the handed-over cpu or its process
//! for a PCI function, its payload endpoint or container, or its process and container for the
//! rendezvous, endpoint transfer, and pages check results. The PCI claim result needs B disjoint from some
//! other domain, which keeps the root container out of B, and the BAR map and unmap results also read the
//! boot-time BAR table, which is not in the view because `kernel_u_new_thread_changed` does not state that it
//! is unchanged. With `trace_ni_at`, steps of A between two states leave B's results unchanged.
//!
//! PCI functions and device memory: a function sits in the page-table function array of the process that owns
//! it, so `domain_view` holds the attach state of exactly the domain's functions. A BAR mapping maps a page or 2M
//! chunk of a BAR of a function its process owns, and `kernel_u_io_leaf_wf` (proved from the kernel invariant)
//! says that every IO leaf maps a BAR page of a function of its process and that no RAM leaf covers a BAR page,
//! so `memory_iso` covers device memory with no further premise.
//!
//! Object pointers and page addresses returned on success come from the shared global
//! allocator and are guaranteed only to be fresh, so which pointer or page a domain receives can
//! depend on allocations by other domains. This allocator channel is outside the proof.
//! `merge_2m` labels its actual quota exchange and has local-respect and isolation obligations.
//! Its fragmentation-dependent returned count is not covered by deterministic output consistency.
#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_kernel_core::*;
use veriflat_u_facts::*;

pub mod domain;
pub mod isolation;
pub mod ni_alloc_quota;
pub mod ni_schedule;
pub mod ni_rebalance;
pub mod ni_cpu_hotplug;
pub mod ni_new_thread;
pub mod ni_new_endpoint;
pub mod ni_mmap_4k;
pub mod ni_unmap_4k;
pub mod ni_mmap_2m;
pub mod ni_unmap_2m;
pub mod ni_mmap_1g;
pub mod ni_unmap_1g;
pub mod ni_iommu_map_4k;
pub mod ni_iommu_unmap_4k;
pub mod ni_ipc;
pub mod ni_new_process;
pub mod ni_new_container;
pub mod ni_share_4k;
pub mod ni_pci;
pub mod ni_pci_bar;
pub mod ni_kill_container;
pub mod ni_kill_process;
pub mod ni_thread_exit;
pub mod ni_trap;
pub mod ni_env;
pub mod theorem;

pub use domain::*;
pub use isolation::*;
pub use theorem::*;

verus! {
global size_of usize == 8;
}
