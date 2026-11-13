//! Round 7: `split_2m` and `merge_2m`, quota exchanges in sections that record no progress. A section starts from the
//! trap path or from the held state the previous one left, the cpu and its running thread write-held by the cpu in its
//! kernel step, and ends there or back on the trap path. The held state is the one the `mmap_4k` hold step leaves, so a
//! held cpu is inside `mmap_4k` for `in_world` and can always release. A call records one section per block.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use crate::family_new_thread::*;
use veriflat_syscall_split_2m::syscall_split_2m::syscall_split_2m_spec::*;
use veriflat_syscall_merge_2m::syscall_merge_2m::syscall_merge_2m_spec::*;

verus! {
pub open spec fn split_merge_label(l: StepLabel) -> bool { l is Split2m || l is Merge2m }

/// One call of this family with its requested block count.
pub ghost enum SplitMergeCall { Split { n: usize }, Merge { n: usize } }

/// `t` is a complete trace of a successful `call` on `c` as its exec contract ensures it: one section per block.
pub open spec fn split_merge_call_trace_ok(call: SplitMergeCall, t: Seq<KernelStep>, c: CpuId) -> bool {
    match call {
        SplitMergeCall::Split { n } => split_2m_syscall_trace(t, c, n, RetValueType::SuccessUsize { value: t.len() as usize }),
        SplitMergeCall::Merge { n } => merge_2m_syscall_trace(t, c, n, RetValueType::SuccessUsize { value: t.len() as usize }),
    }
}

pub open spec fn split_merge_call_bound(call: SplitMergeCall) -> nat {
    match call { SplitMergeCall::Split { n } => n as nat, SplitMergeCall::Merge { n } => n as nat }
}

pub proof fn split_merge_call_trace_ok_implies_len_bounded(call: SplitMergeCall, t: Seq<KernelStep>, c: CpuId)
    requires split_merge_call_trace_ok(call, t, c),
    ensures t.len() <= split_merge_call_bound(call),
{
    reveal(split_2m_syscall_trace); reveal(merge_2m_syscall_trace);
}

/// A section of `d` keeps every other write-locked cpu, every object lock, and every pagetable, records no progress, and
/// leaves `d` on the trap path or with its cpu and running thread write-held in its kernel step.
pub proof fn split_merge_step_implies_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), split_merge_label(l), labeled_step(l, u, u2, d),
    ensures
        others_kept(u, u2, d), object_locks_same(u, u2), tables_kept(u, u2), !table_op(u, d), !table_op(u2, d), op_in_step_kept(u, u2, d),
        !in_new_endpoint(u2, d), !in_new_thread(u2, d), !table_killer(u, d), !table_killer(u2, d), !table_sharer(u, d), !table_sharer(u2, d), !crate::family_exit::in_exit(u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    let ud = u.cpu_array[d as int];
    assert(u.thread_map[ud.current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: d }));
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by {
        let ux = u.cpu_array[x as int];
        if ux.current_thread is Some && ux.current_thread == ud.current_thread { assert(u.thread_map[ux.current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: x })); }
    };
}
} // verus!
