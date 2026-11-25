//! User-memory model: physical memory and per-cpu store buffers around the kernel's user-visible steps, and noninterference
//! over them.
//!
//! The machine. A `MemState` is the user state `KernelU` of the kernel, a total map from physical byte addresses to bytes
//! (`mem`), and one FIFO store buffer per cpu (`bufs`, oldest first); store buffers and memory are top-level components, not
//! part of a cpu record. A step `mem_step(old, new, label, cpu)` is one of
//! - `Kernel { label }`: `labeled_step(label, old.u, new.u, cpu)` of the noninterference crate; the buffers of the drain set
//!   (`drained`) are written to memory in some interleaving that keeps each cpu's own order, oldest first, and fixes none
//!   between cpus (`drain_order`; increasing cpu id is one, `increasing_cpu_drain_implies_kernel_mem_step`), and emptied; at
//!   the three mmap leaf steps (`Mmap4kLeaf`, `Mmap2mLeaf`, `Mmap1gLeaf`) the frame of the installed leaf is then zeroed. The
//!   drain set is empty for the eight hardware labels (trap enter, return, divert, register and return-value writes, CPU and
//!   IOMMU TLB fills, context cache fills); for every other label it is the acting cpu together with every other cpu whose
//!   TLB (a key added, removed, or changed), mode (`op`), or current process the step changes.
//! - `StoreIssued { s }`: a cpu in user mode buffers a store through a writable translation of its current process's PCID,
//!   which keys a TLB of that cpu.
//! - `StoreCommitted`: the oldest store of a cpu's buffer is written to memory and leaves the buffer.
//! - `Load { .. }`: a cpu in user mode reads through a translation of its current process's PCID; each byte is the youngest
//!   buffered store of that cpu covering it, else memory. Nothing changes.
//! - `DmaWritten { .. }`: a device writes arbitrary bytes through a writable 4K IOTLB entry of its domain, which the IOTLB
//!   holds, in one step.
//! The user and device steps leave `u` unchanged.
//!
//! Hypotheses. The model is the machine above under the following hardware rules, which its definition encodes and which are
//! assumed, not proved:
//! - H1: every kernel-label step executes a LOCKed or serializing instruction on its cpu before any user-visible effect, so
//!   the acting cpu's buffer is drained.
//! - H2: a kernel step changes a remote cpu's TLB, mode, or current process only through an interrupt to that cpu, whose
//!   delivery drains that cpu's buffer.
//! - H3: buffers are FIFO; loads forward from the youngest matching store; `syscall`, `sysret`, and TLB fills do not drain.
//! - H4: every device write lands while the IOTLB entry translating it is present (VT-d drains on invalidation).
//! - H5: the kernel writes user memory only by zeroing at the three mmap leaf steps.
//! - H7: every state satisfies the user-level well-formedness the other proof crates assume (`kernel_u_ownership_wf`) and
//!   `kernel_u_current_tlb_matches_present_wf` (a cpu's TLB under its current process's PCID agrees with every present leaf
//!   of that process's table), and buffers start empty. Both hold in the user projection of every kernel state satisfying
//!   the kernel invariant: `kernel_wf_implies_u_ownership_wf` and `kernel_inv_implies_u_current_tlb_matches_present_wf` of
//!   the user-level facts crate (`noninterference/u_facts`).
//! From H7 a CPU TLB fill under a non-default PCID never replaces a translation that TLB already caches with a different one
//! (`current_tlb_matches_present_implies_fill_keeps_cached_translations`).
//!
//! Proved (`invariant`): `store_buffers_covered`, every buffered store is covered by a writable translation of its cpu's
//! current process's PCID and that cpu is neither inside a kernel step nor off, holds at every index of every behaviour
//! from empty buffers; so every commit and drain writes only inside the frame its writer's own writable translation names,
//! every device write only inside a frame a writable IOTLB entry of its domain names, and a cpu inside a kernel step or off
//! has an empty buffer. Every byte that changes across a step changes by a commit or drain of such a store, by a device
//! write, or by the zeroing of an mmap leaf step, and right after an mmap leaf step the installed frame is all zero. The
//! per-label fact that a kernel step keeps the PCID of every process alive before and after it is proved from the step
//! specifications (`pcid`). In the user projection of a kernel satisfying the kernel invariant (`mapped`), every pending
//! store targets a frame that a leaf of its writer's page table maps at the store's VA (a BAR page, or a page in the mapped
//! state of the store's size listing that table and VA), and every device write targets a Mapped4k page listing the
//! domain's IOMMU table and the IOVA.
//!
//! Noninterference over memory (`ni`). The memory view `mem_domain_view(st, root)` of a domain is its `domain_view`, the
//! store buffer of each of its cpus, and every physical byte that a 4K, 2M, or 1G page-table leaf or 4K IOMMU-table leaf of
//! one of its processes maps (`domain_maps_byte`); TLBs are not in the view, and the only isolation invariant is the
//! noninterference crate's `isolated`. A step of cpu `c` of `x` toward `y` is taken under `mem_ni_step`: the user-level
//! facts `kernel_u_ownership_wf` (both states), `kernel_u_current_tlb_matches_present_wf` and
//! `kernel_u_iotlb_matches_present_wf` (all three proved from the kernel invariant in `noninterference/u_facts`, and the
//! leaf alignment `kernel_u_leaf_addr_aligned_wf` follows from the first), `store_buffers_covered` (proved above), the step
//! itself, its attribution to `x` (`mem_step_in_domain`: a fill of any domain, a device write of a DID whose anchor owner is
//! a process of `x`, any other step of a cpu of `x`), the honest-peer conditions of the noninterference crate
//! (`ni_honest_peer`), and one premise, `hidden_translations_outside(u, x, y)`: a translation of the current key of a cpu of
//! `x` at a VA where its current process has no leaf of that size, and a 4K IOTLB translation of a DID of `x` at an IOVA
//! where the anchor owner's IOMMU table has no leaf, name no byte `y` maps. These are the hidden leaves of an unmap, kill, or
//! exit not yet flushed. That a kernel step of `x` drains no buffer holding stores of a cpu outside `x` but its own
//! (`drains_within_domain`) is proved for every label (`drain`): a step of `x` changes the TLBs, mode, or current process of
//! no other cpu outside `x` unless that cpu is inside a kernel step or off, and such a cpu has an empty buffer
//! (`store_buffers_covered`); the kill TLB clear changes the TLBs of a cpu inside a kernel step or running the kill target,
//! whose container lies in the killer's domain.
//! Theorems: `mem_step_implies_view_kept_and_isolated` (a step of `x` keeps `isolated(x, y)` and the memory view of `y`),
//! `third_domain_mem_step_implies_views_kept_and_isolated`, `mem_trace_ni_at` (traces of two domains),
//! `pairwise_isolated_domains_mem_trace_implies_isolated_and_view_unchanged`, and `equal_mem_views_implies_equal_load_value`
//! (equal memory views give equal loads through a translation of a leaf the loading process has; loads through hidden
//! translations are not covered).
//!
//! Not proved: the hypotheses above and `hidden_translations_outside`; that loads return any particular value beyond the
//! forwarding rule and the load theorem; anything about IOMMU translations other than the IOTLB entry a device write uses;
//! the zero-fill of pages other than mmap leaves.
//!
//! Relation to the kernel. The kernel's four pending-write events change no U state (`kernel_k_*_implies_u_unchanged` in
//! `src/kernel/kernel_step_wrappers/env_steps.rs`). Main's `KernelK` now carries its own ghost pending-store and pending-DMA
//! sets with the safety theorem `kernel_inv_implies_pending_writes_target_mapped_or_bar_pages`; this crate's `bufs` is a
//! separate, richer model (FIFO buffers with bytes) that no theorem connects to the kernel's sets. H1, H2, and H4 correspond
//! to the trusted ensures of the kernel's `enter_step`, of its remote flushes and running-to-idle IPI, and of its IOTLB
//! invalidations.
#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_kernel_core::*;
use veriflat_u_facts::*;
use veriflat_noninterference::{StepLabel, labeled_step};

pub mod state;
pub mod step;
pub mod pcid;
pub mod invariant;
pub mod mapped;
pub mod ni;
pub mod drain;

pub use state::*;
// The kernel's own `PendingStore` (main's ghost store buffers) also comes in through `veriflat_kernel_core::*`; this crate means its own.
pub use state::PendingStore;
pub use step::*;

verus! {
global size_of usize == 8;
}
