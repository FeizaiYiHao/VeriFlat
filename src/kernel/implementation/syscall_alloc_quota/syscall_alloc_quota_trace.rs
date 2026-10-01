use vstd::prelude::*;
use crate::*;
use super::syscall_alloc_quota_spec::*;
verus! {
/// The quota wrapper's user-view facts are exactly the quota step on `pre`/`post`.
pub(super) proof fn alloc_quota_4k_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, alloc_amount: usize)
    requires
        kernel_u_only_process_quota_4k_changed(pre, post, cpu_id, process_ptr, container_ptr, alloc_amount as int),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.owning_container == container_ptr
            &&& pre.container_map.dom().contains(container_ptr)
            &&& pre.container_map.spec_index(container_ptr).lock_state is Unlocked
            &&& !pre.container_map.spec_index(container_ptr).killed
            &&& pre.container_map.spec_index(container_ptr).quota_4k >= alloc_amount as int
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& !pre.process_map.spec_index(process_ptr).killed
            &&& pre.process_map.spec_index(process_ptr).quota_4k + alloc_amount as int <= usize::MAX
            &&& alloc_amount > 0
        },
    ensures
        alloc_quota_4k_step_pre(pre, cpu_id, alloc_amount),
        alloc_quota_4k_step(pre, post, cpu_id, alloc_amount),
{ reveal(alloc_quota_4k_step_pre); }

/// The one step pushed since `before` is the complete successful trace.
pub(super) proof fn alloc_quota_4k_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, alloc_amount: usize)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        alloc_amount > 0,
        alloc_quota_4k_step_pre(pre, cpu_id, alloc_amount),
        alloc_quota_4k_step(pre, post, cpu_id, alloc_amount),
    ensures
        alloc_quota_4k_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, alloc_amount, RetValueType::Success),
{ reveal(alloc_quota_4k_syscall_trace); }

/// A rejected or zero-amount call records no step.
pub(super) proof fn alloc_quota_4k_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success && alloc_amount > 0),
    ensures
        alloc_quota_4k_syscall_trace(trace, pre, pre, cpu_id, alloc_amount, ret),
{ reveal(alloc_quota_4k_syscall_trace); }
} // verus!
