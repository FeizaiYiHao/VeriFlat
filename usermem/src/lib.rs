//! User-memory model, stage 1: physical memory and per-cpu store buffers around the kernel's user-visible steps.
//!
//! The machine. A `MemState` is the user state `KernelU` of the kernel, a total map from physical byte addresses to bytes
//! (`mem`), and one FIFO store buffer per cpu (`bufs`, oldest first); store buffers and memory are top-level components, not
//! part of a cpu record. A step `mem_step(old, new, label, cpu)` is one of
//! - `Kernel { label }`: `labeled_step(label, old.u, new.u, cpu)` of the noninterference crate; the buffers of the drain set
//!   (`drained`) are written to memory, cpu by cpu in increasing id and each oldest first, and emptied; at the three mmap leaf
//!   steps (`Mmap4kLeaf`, `Mmap2mLeaf`, `Mmap1gLeaf`) the frame of the installed leaf is then zeroed. The drain set is empty for
//!   the eight hardware labels (trap enter, return, divert, register and return-value writes, CPU and IOMMU TLB fills, context
//!   cache fills); for every other label it is the acting cpu together with every other cpu whose TLB, mode (`op`), or current
//!   process the step changes.
//! - `StoreIssued { s }`: a cpu in user mode buffers a store through a writable translation of its current process's PCID.
//! - `StoreCommitted`: the oldest store of a cpu's buffer is written to memory and leaves the buffer.
//! - `Load { .. }`: a cpu in user mode reads through a translation of its current process's PCID; each byte is the youngest
//!   buffered store of that cpu covering it, else memory. Nothing changes.
//! - `DmaWritten { .. }`: a device writes arbitrary bytes through a writable 4K IOTLB entry of its domain, in one step.
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
//! - H7: every state satisfies the user-level well-formedness the other proof crates assume (`kernel_u_ownership_wf`), and
//!   buffers start empty.
//! In addition the theorems take one hypothesis about the kernel's user state that the user-level facts do not yet provide,
//! `cpu_tlb_fill_keeps_cached_translations`: a CPU TLB fill under a non-default PCID never replaces a translation that TLB
//! already caches with a different one. A later stage derives it from the kernel invariants.
//!
//! Proved (`invariant`): `store_buffers_covered`, every buffered store is covered by a writable translation of its cpu's
//! current process's PCID and that cpu is neither inside a kernel step nor off, holds at every index of every behaviour
//! from empty buffers; so every commit and drain writes only inside the frame its writer's own writable translation names,
//! every device write only inside a frame a writable IOTLB entry of its domain names, and a cpu inside a kernel step or off
//! has an empty buffer. Every byte that changes across a step changes by a commit or drain of such a store, by a device
//! write, or by the zeroing of an mmap leaf step, and right after an mmap leaf step the installed frame is all zero. The
//! per-label fact that a kernel step keeps the PCID of every process alive before and after it is proved from the step
//! specifications (`pcid`).
//!
//! Not proved: the hypotheses above; that loads return any particular value beyond the forwarding rule; anything about
//! which process may read or write which frame (isolation of user memory) or about IOMMU translations other than the IOTLB
//! entry a device write uses; the zero-fill of pages other than mmap leaves.
#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_kernel_core::*;
use veriflat_u_facts::*;
use veriflat_noninterference::{StepLabel, labeled_step};

pub mod state;
pub mod step;
pub mod pcid;
pub mod invariant;

pub use state::*;
pub use step::*;

verus! {
global size_of usize == 8;
}
