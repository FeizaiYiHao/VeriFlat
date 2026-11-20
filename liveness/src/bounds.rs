//! Per-call step bounds for `syscall_thread_exit`, `syscall_kill_process`, and the BAR map and unmap syscalls.
//!
//! The BAR syscalls (`syscall_map_pci_bar_4k`, `_2m`, `syscall_unmap_pci_bar_4k`, `_2m`) are not in the world; their
//! complete trace specs bound their length, which the theorems read out.
//!
//! `thread_exit` (round 13): the trace spec carries the bound its exec contract fixes at entry,
//! `thread_exit_step_bound(k, cpu_id) = thread_exit_reclaim_step_bound() + 40 + 34 * thread_exit_entry_call_depth(k, cpu_id)`,
//! so the theorem only reads it out.
//!
//! `kill_process`: the table-phase steps are bounded by the kernel relative to the retired targets; the other steps stay
//! relative to the trace.
use vstd::prelude::*;
use crate::*;
use veriflat_syscall_thread_exit::syscall_thread_exit::syscall_thread_exit_spec::*;
use veriflat_syscall_kill_process::syscall_kill_process::syscall_kill_process_spec::*;
use veriflat_syscall_pci_bar::syscall_pci_bar::syscall_pci_bar_spec::*;

verus! {

// ---------------------------------------------------------------------------------------------------------------------
// thread_exit.

/// Per-call bound of `syscall_thread_exit`: its complete trace records at most the bound its exec contract fixes at entry,
/// `thread_exit_step_bound(*old(krnl), cpu_id)`, whether or not the thread exits.
pub proof fn thread_exit_syscall_trace_implies_len_bounded(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, c: CpuId, exited: bool, bound: nat)
    requires thread_exit_syscall_trace(trace, pre, post, c, exited, bound),
    ensures trace.len() <= bound,
{ reveal(thread_exit_syscall_trace); }

// ---------------------------------------------------------------------------------------------------------------------
// kill_process.

/// Steps after the first outside the table phase: walking, locking and marking, and the thread stage.
pub open spec fn kill_process_other_count(t: Seq<KernelStep>, c: CpuId) -> nat
    decreases t.len(),
{ if t.len() <= 1 { 0 } else { kill_process_other_count(t.drop_last(), c) + if kill_process_table_phase_step(t.last(), c) { 0nat } else { 1nat } } }

proof fn kill_process_len_implies_phase_counts(t: Seq<KernelStep>, c: CpuId)
    requires 1 <= t.len(),
    ensures t.len() == 1 + kill_process_table_count(t, c) + kill_process_other_count(t, c),
    decreases t.len(),
{
    reveal(kill_process_table_count);
    if t.len() > 1 { kill_process_len_implies_phase_counts(t.drop_last(), c); }
}

/// Per-call bound of `syscall_kill_process`, relative to the retired targets and the steps outside the table phase.
/// Its right-hand side still counts steps of the trace because no bound is fixed at entry. A victim's chain of killed
/// callers is bounded only by its head's call depth when the walk locks it, and other cpus can raise that depth by IPC
/// calls before then.
pub proof fn kill_process_syscall_trace_implies_len_bounded(trace: Seq<KernelStep>, pre: KernelU, post: KernelU, c: CpuId, child_index: usize)
    requires kill_process_syscall_trace(trace, pre, post, c, child_index, true),
    ensures
        trace.len() <= 2 + kill_process_target_step_bound() * kill_process_retire_count(trace.drop_last(), c) + kill_process_other_count(trace.drop_last(), c),
{
    reveal(kill_process_syscall_trace); reveal(kill_process_partial_trace);
    kill_process_len_implies_phase_counts(trace.drop_last(), c);
}

// ---------------------------------------------------------------------------------------------------------------------
// BAR map and unmap.

/// A successful 4K BAR map records at most five steps: enter, one directory step per missing L4, L3, and L2 entry, and exit.
pub proof fn map_pci_bar_4k_syscall_trace_implies_len_bounded(trace: Seq<KernelStep>, c: CpuId, slot: usize, page_index: usize, va: VAddr)
    requires map_pci_bar_4k_syscall_trace(trace, c, slot, page_index, va),
    ensures trace.len() <= 5,
{ reveal(map_pci_bar_4k_syscall_trace); }

/// A successful 2M BAR map records at most `NUM_CPUS + 4` steps: enter, its directory and empty-L1 steps, and exit.
pub proof fn map_pci_bar_2m_syscall_trace_implies_len_bounded(trace: Seq<KernelStep>, c: CpuId, slot: usize, index: usize, va: VAddr)
    requires map_pci_bar_2m_syscall_trace(trace, c, slot, index, va),
    ensures trace.len() <= NUM_CPUS + 4,
{ reveal(map_pci_bar_2m_syscall_trace); }

/// A successful 4K BAR unmap records at most `NUM_CPUS + 3` steps: hide, one TLB flush per cpu, flushed, and exit.
pub proof fn unmap_pci_bar_4k_syscall_trace_implies_len_bounded(trace: Seq<KernelStep>, c: CpuId, va: VAddr)
    requires unmap_pci_bar_4k_syscall_trace(trace, c, va),
    ensures trace.len() <= NUM_CPUS + 3,
{ reveal(unmap_pci_bar_4k_syscall_trace); }

/// A successful 2M BAR unmap records at most `NUM_CPUS + 3` steps: hide, one TLB flush per cpu, flushed, and exit.
pub proof fn unmap_pci_bar_2m_syscall_trace_implies_len_bounded(trace: Seq<KernelStep>, c: CpuId, va: VAddr)
    requires unmap_pci_bar_2m_syscall_trace(trace, c, va),
    ensures trace.len() <= NUM_CPUS + 3,
{ reveal(unmap_pci_bar_2m_syscall_trace); }

} // verus!
