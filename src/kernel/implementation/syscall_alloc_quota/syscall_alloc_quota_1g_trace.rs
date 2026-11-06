use vstd::prelude::*;
use crate::*;
use super::syscall_alloc_quota_1g_spec::*;
verus! {
/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn alloc_quota_1g_result_from_k(krnl: &KernelK, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let ctn_ptr = cpu.view().view().owning_container;
            let prc_ptr = cpu.view().view().current_process->Some_0;
            let container = krnl.ctn_mp.spec_index(ctn_ptr);
            let process = krnl.prc_mp.spec_index(prc_ptr);
            let quota = krnl.allc_1g_mp.spec_index(container.view_rodata().view().allocator_ptr_1g).quota.view().value;
            let owner = container.lock_process_owner_u();
            let conflict = owner is Some && owner->Some_0 < LockOwnerId::Some(process.view_rodata().view().depth);
            let unblocked = !container.being_killed() && !conflict;
            let live = unblocked && !container.view().zombie && !process.being_killed();
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_process is Some
            &&& !(ret is CpuIdle) ==> krnl.ctn_mp.dom().contains(ctn_ptr) && krnl.prc_mp.dom().contains(prc_ptr)
            &&& ret is ErrorContainerKilled ==> container.being_killed()
            &&& ret is ErrorContainerLockOrderConflict ==> !container.being_killed() && conflict
            &&& ret is ErrorContainerZombie ==> unblocked && container.view().zombie
            &&& ret is ErrorProcessKilled ==> unblocked && !container.view().zombie && process.being_killed()
            &&& ret is ErrorContainerQuotaInsufficient ==> live && quota < alloc_amount
            &&& ret is ErrorProcessQuotaOverflow ==> live && quota >= alloc_amount && alloc_amount > usize::MAX - process.view().quota_1g
            &&& ret is Success ==> live && quota >= alloc_amount && alloc_amount <= usize::MAX - process.view().quota_1g
            &&& ret is CpuIdle || ret is ErrorContainerKilled || ret is ErrorContainerLockOrderConflict || ret is ErrorContainerZombie || ret is ErrorProcessKilled
                || ret is ErrorContainerQuotaInsufficient || ret is ErrorProcessQuotaOverflow || ret is Success
        },
    ensures
        alloc_quota_1g_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.ctn_mp.dom().contains(c.owning_container) { kernel_container_projection_at(krnl, c.owning_container); }
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) { kernel_process_projection_at(krnl, c.current_process->Some_0); }
}

/// The quota wrapper's user-view facts are exactly the quota step on `pre`/`post`.
pub(super) proof fn alloc_quota_1g_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, alloc_amount: usize)
    requires
        kernel_u_only_process_quota_1g_changed(pre, post, cpu_id, prc_ptr, ctn_ptr, alloc_amount as int),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(prc_ptr)
            &&& cpu.owning_container == ctn_ptr
            &&& pre.container_map.dom().contains(ctn_ptr)
            &&& pre.container_map.spec_index(ctn_ptr).lock_state is Unlocked
            &&& !pre.container_map.spec_index(ctn_ptr).killed
            &&& !pre.container_map.spec_index(ctn_ptr).zombie
            &&& pre.container_map.spec_index(ctn_ptr).quota_1g >= alloc_amount as int
            &&& pre.process_map.dom().contains(prc_ptr)
            &&& pre.process_map.spec_index(prc_ptr).lock_state is Unlocked
            &&& !pre.process_map.spec_index(prc_ptr).killed
            &&& pre.process_map.spec_index(prc_ptr).quota_1g + alloc_amount as int <= usize::MAX
            &&& alloc_amount > 0
        },
    ensures
        alloc_quota_1g_step_pre(pre, cpu_id, alloc_amount),
        alloc_quota_1g_step(pre, post, cpu_id, alloc_amount),
{ reveal(alloc_quota_1g_step_pre); }

/// The one step pushed since `before` is the complete successful trace.
pub(super) proof fn alloc_quota_1g_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, alloc_amount: usize)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        alloc_amount > 0,
        alloc_quota_1g_step_pre(pre, cpu_id, alloc_amount),
        alloc_quota_1g_step(pre, post, cpu_id, alloc_amount),
    ensures
        alloc_quota_1g_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, alloc_amount, RetValueType::Success),
{ reveal(alloc_quota_1g_syscall_trace); }

/// A rejected or zero-amount call records no step.
pub(super) proof fn alloc_quota_1g_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success && alloc_amount > 0),
    ensures
        alloc_quota_1g_syscall_trace(trace, pre, pre, cpu_id, alloc_amount, ret),
{ reveal(alloc_quota_1g_syscall_trace); }

/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn alloc_thread_quota_1g_result_from_k(krnl: &KernelK, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let prc_ptr = cpu.view().view().current_process->Some_0;
            let thrd_ptr = cpu.view().view().current_thread->Some_0;
            let process = krnl.prc_mp.spec_index(prc_ptr);
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            let live = !process.being_killed() && krnl.thrd_mp.dom().contains(thrd_ptr) && !thread.being_killed();
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_process is Some && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.prc_mp.dom().contains(prc_ptr)
            &&& ret is ErrorProcessKilled ==> process.being_killed()
            &&& ret is ErrorThreadKilled ==> !process.being_killed() && krnl.thrd_mp.dom().contains(thrd_ptr) && thread.being_killed()
            &&& ret is ErrorNoQuota ==> live && process.view().quota_1g < alloc_amount
            &&& ret is ErrorThreadQuotaOverflow ==> live && process.view().quota_1g >= alloc_amount && alloc_amount > usize::MAX - thread.view().quota_1g
            &&& ret is Success ==> live && process.view().quota_1g >= alloc_amount && alloc_amount <= usize::MAX - thread.view().quota_1g
            &&& ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorNoQuota || ret is ErrorThreadQuotaOverflow || ret is Success
        },
    ensures
        alloc_thread_quota_1g_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) { kernel_process_projection_at(krnl, c.current_process->Some_0); }
    if krnl.thrd_mp.dom().contains(c.current_thread->Some_0) { kernel_thread_projection_at(krnl, c.current_thread->Some_0); }
}

/// The thread quota wrapper's user-view facts are exactly the thread quota step on `pre`/`post`.
pub(super) proof fn alloc_thread_quota_1g_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, alloc_amount: usize)
    requires
        kernel_u_only_process2thread_quota_1g_changed(pre, post, cpu_id, prc_ptr, thrd_ptr, alloc_amount as int),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(prc_ptr)
            &&& cpu.current_thread == Some(thrd_ptr)
            &&& pre.process_map.dom().contains(prc_ptr)
            &&& pre.process_map.spec_index(prc_ptr).lock_state is Unlocked
            &&& !pre.process_map.spec_index(prc_ptr).killed
            &&& pre.process_map.spec_index(prc_ptr).quota_1g >= alloc_amount as int
            &&& pre.thread_map.dom().contains(thrd_ptr)
            &&& pre.thread_map.spec_index(thrd_ptr).lock_state is Unlocked
            &&& !pre.thread_map.spec_index(thrd_ptr).killed
            &&& pre.thread_map.spec_index(thrd_ptr).quota_1g + alloc_amount as int <= usize::MAX
            &&& alloc_amount > 0
        },
    ensures
        alloc_thread_quota_1g_step_pre(pre, cpu_id, alloc_amount),
        alloc_thread_quota_1g_step(pre, post, cpu_id, alloc_amount),
{ reveal(alloc_thread_quota_1g_step_pre); }

/// The one step pushed since `before` is the complete successful trace.
pub(super) proof fn alloc_thread_quota_1g_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, alloc_amount: usize)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        alloc_amount > 0,
        alloc_thread_quota_1g_step_pre(pre, cpu_id, alloc_amount),
        alloc_thread_quota_1g_step(pre, post, cpu_id, alloc_amount),
    ensures
        alloc_thread_quota_1g_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, alloc_amount, RetValueType::Success),
{ reveal(alloc_thread_quota_1g_syscall_trace); }

/// A rejected or zero-amount call records no step.
pub(super) proof fn alloc_thread_quota_1g_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success && alloc_amount > 0),
    ensures
        alloc_thread_quota_1g_syscall_trace(trace, pre, pre, cpu_id, alloc_amount, ret),
{ reveal(alloc_thread_quota_1g_syscall_trace); }
} // verus!
