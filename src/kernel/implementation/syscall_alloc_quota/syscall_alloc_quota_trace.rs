use vstd::prelude::*;
use crate::*;
use super::syscall_alloc_quota_spec::*;
verus! {
/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn alloc_quota_4k_result_from_k(krnl: &KernelK, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let container_ptr = cpu.view().view().owning_container;
            let process_ptr = cpu.view().view().current_process->Some_0;
            let container = krnl.ctn_mp.spec_index(container_ptr);
            let process = krnl.prc_mp.spec_index(process_ptr);
            let quota = krnl.allc_4k_mp.spec_index(container.view_rodata().view().allocator_ptr_4k).quota.view().value;
            let live = !container.being_killed() && !container.view().zombie && !process.being_killed();
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_process is Some
            &&& !(ret is CpuIdle) ==> krnl.ctn_mp.dom().contains(container_ptr) && krnl.prc_mp.dom().contains(process_ptr)
            &&& ret is ErrorContainerKilled ==> container.being_killed()
            &&& ret is ErrorContainerZombie ==> !container.being_killed() && container.view().zombie
            &&& ret is ErrorProcessKilled ==> !container.being_killed() && !container.view().zombie && process.being_killed()
            &&& ret is ErrorContainerQuotaInsufficient ==> live && quota < alloc_amount
            &&& ret is ErrorProcessQuotaOverflow ==> live && quota >= alloc_amount && alloc_amount > usize::MAX - process.view().quota_4k
            &&& ret is Success ==> live && quota >= alloc_amount && alloc_amount <= usize::MAX - process.view().quota_4k
            &&& ret is CpuIdle || ret is ErrorContainerKilled || ret is ErrorContainerZombie || ret is ErrorProcessKilled || ret is ErrorContainerQuotaInsufficient || ret is ErrorProcessQuotaOverflow || ret is Success
        },
    ensures
        alloc_quota_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.ctn_mp.dom().contains(c.owning_container) { kernel_container_projection_at(krnl, c.owning_container); }
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) { kernel_process_projection_at(krnl, c.current_process->Some_0); }
}

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
            &&& !pre.container_map.spec_index(container_ptr).zombie
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

/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn alloc_thread_quota_4k_result_from_k(krnl: &KernelK, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let process_ptr = cpu.view().view().current_process->Some_0;
            let thread_ptr = cpu.view().view().current_thread->Some_0;
            let process = krnl.prc_mp.spec_index(process_ptr);
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let live = !process.being_killed() && krnl.thr_mp.dom().contains(thread_ptr) && !thread.being_killed();
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_process is Some && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.prc_mp.dom().contains(process_ptr)
            &&& ret is ErrorProcessKilled ==> process.being_killed()
            &&& ret is ErrorThreadKilled ==> !process.being_killed() && krnl.thr_mp.dom().contains(thread_ptr) && thread.being_killed()
            &&& ret is ErrorNoQuota ==> live && process.view().quota_4k < alloc_amount
            &&& ret is ErrorThreadQuotaOverflow ==> live && process.view().quota_4k >= alloc_amount && alloc_amount > usize::MAX - thread.view().quota_4k
            &&& ret is Success ==> live && process.view().quota_4k >= alloc_amount && alloc_amount <= usize::MAX - thread.view().quota_4k
            &&& ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorNoQuota || ret is ErrorThreadQuotaOverflow || ret is Success
        },
    ensures
        alloc_thread_quota_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) { kernel_process_projection_at(krnl, c.current_process->Some_0); }
    if krnl.thr_mp.dom().contains(c.current_thread->Some_0) { kernel_thread_projection_at(krnl, c.current_thread->Some_0); }
}

/// The thread quota wrapper's user-view facts are exactly the thread quota step on `pre`/`post`.
pub(super) proof fn alloc_thread_quota_4k_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, alloc_amount: usize)
    requires
        kernel_u_only_process2thread_quota_4k_changed(pre, post, cpu_id, process_ptr, thread_ptr, alloc_amount as int),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& !pre.process_map.spec_index(process_ptr).killed
            &&& pre.process_map.spec_index(process_ptr).quota_4k >= alloc_amount as int
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& pre.thread_map.spec_index(thread_ptr).lock_state is Unlocked
            &&& !pre.thread_map.spec_index(thread_ptr).killed
            &&& pre.thread_map.spec_index(thread_ptr).quota_4k + alloc_amount as int <= usize::MAX
            &&& alloc_amount > 0
        },
    ensures
        alloc_thread_quota_4k_step_pre(pre, cpu_id, alloc_amount),
        alloc_thread_quota_4k_step(pre, post, cpu_id, alloc_amount),
{ reveal(alloc_thread_quota_4k_step_pre); }

/// The one step pushed since `before` is the complete successful trace.
pub(super) proof fn alloc_thread_quota_4k_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, alloc_amount: usize)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        alloc_amount > 0,
        alloc_thread_quota_4k_step_pre(pre, cpu_id, alloc_amount),
        alloc_thread_quota_4k_step(pre, post, cpu_id, alloc_amount),
    ensures
        alloc_thread_quota_4k_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, alloc_amount, RetValueType::Success),
{ reveal(alloc_thread_quota_4k_syscall_trace); }

/// A rejected or zero-amount call records no step.
pub(super) proof fn alloc_thread_quota_4k_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success && alloc_amount > 0),
    ensures
        alloc_thread_quota_4k_syscall_trace(trace, pre, pre, cpu_id, alloc_amount, ret),
{ reveal(alloc_thread_quota_4k_syscall_trace); }

/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn alloc_quota_2m_result_from_k(krnl: &KernelK, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let container_ptr = cpu.view().view().owning_container;
            let process_ptr = cpu.view().view().current_process->Some_0;
            let container = krnl.ctn_mp.spec_index(container_ptr);
            let process = krnl.prc_mp.spec_index(process_ptr);
            let quota = krnl.allc_2m_mp.spec_index(container.view_rodata().view().allocator_ptr_2m).quota.view().value;
            let live = !container.being_killed() && !container.view().zombie && !process.being_killed();
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_process is Some
            &&& !(ret is CpuIdle) ==> krnl.ctn_mp.dom().contains(container_ptr) && krnl.prc_mp.dom().contains(process_ptr)
            &&& ret is ErrorContainerKilled ==> container.being_killed()
            &&& ret is ErrorContainerZombie ==> !container.being_killed() && container.view().zombie
            &&& ret is ErrorProcessKilled ==> !container.being_killed() && !container.view().zombie && process.being_killed()
            &&& ret is ErrorContainerQuotaInsufficient ==> live && quota < alloc_amount
            &&& ret is ErrorProcessQuotaOverflow ==> live && quota >= alloc_amount && alloc_amount > usize::MAX - process.view().quota_2m
            &&& ret is Success ==> live && quota >= alloc_amount && alloc_amount <= usize::MAX - process.view().quota_2m
            &&& ret is CpuIdle || ret is ErrorContainerKilled || ret is ErrorContainerZombie || ret is ErrorProcessKilled || ret is ErrorContainerQuotaInsufficient || ret is ErrorProcessQuotaOverflow || ret is Success
        },
    ensures
        alloc_quota_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.ctn_mp.dom().contains(c.owning_container) { kernel_container_projection_at(krnl, c.owning_container); }
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) { kernel_process_projection_at(krnl, c.current_process->Some_0); }
}

/// The quota wrapper's user-view facts are exactly the quota step on `pre`/`post`.
pub(super) proof fn alloc_quota_2m_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, alloc_amount: usize)
    requires
        kernel_u_only_process_quota_2m_changed(pre, post, cpu_id, process_ptr, container_ptr, alloc_amount as int),
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
            &&& !pre.container_map.spec_index(container_ptr).zombie
            &&& pre.container_map.spec_index(container_ptr).quota_2m >= alloc_amount as int
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& !pre.process_map.spec_index(process_ptr).killed
            &&& pre.process_map.spec_index(process_ptr).quota_2m + alloc_amount as int <= usize::MAX
            &&& alloc_amount > 0
        },
    ensures
        alloc_quota_2m_step_pre(pre, cpu_id, alloc_amount),
        alloc_quota_2m_step(pre, post, cpu_id, alloc_amount),
{ reveal(alloc_quota_2m_step_pre); }

/// The one step pushed since `before` is the complete successful trace.
pub(super) proof fn alloc_quota_2m_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, alloc_amount: usize)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        alloc_amount > 0,
        alloc_quota_2m_step_pre(pre, cpu_id, alloc_amount),
        alloc_quota_2m_step(pre, post, cpu_id, alloc_amount),
    ensures
        alloc_quota_2m_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, alloc_amount, RetValueType::Success),
{ reveal(alloc_quota_2m_syscall_trace); }

/// A rejected or zero-amount call records no step.
pub(super) proof fn alloc_quota_2m_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success && alloc_amount > 0),
    ensures
        alloc_quota_2m_syscall_trace(trace, pre, pre, cpu_id, alloc_amount, ret),
{ reveal(alloc_quota_2m_syscall_trace); }

/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn alloc_thread_quota_2m_result_from_k(krnl: &KernelK, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let process_ptr = cpu.view().view().current_process->Some_0;
            let thread_ptr = cpu.view().view().current_thread->Some_0;
            let process = krnl.prc_mp.spec_index(process_ptr);
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let live = !process.being_killed() && krnl.thr_mp.dom().contains(thread_ptr) && !thread.being_killed();
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_process is Some && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.prc_mp.dom().contains(process_ptr)
            &&& ret is ErrorProcessKilled ==> process.being_killed()
            &&& ret is ErrorThreadKilled ==> !process.being_killed() && krnl.thr_mp.dom().contains(thread_ptr) && thread.being_killed()
            &&& ret is ErrorNoQuota ==> live && process.view().quota_2m < alloc_amount
            &&& ret is ErrorThreadQuotaOverflow ==> live && process.view().quota_2m >= alloc_amount && alloc_amount > usize::MAX - thread.view().quota_2m
            &&& ret is Success ==> live && process.view().quota_2m >= alloc_amount && alloc_amount <= usize::MAX - thread.view().quota_2m
            &&& ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorNoQuota || ret is ErrorThreadQuotaOverflow || ret is Success
        },
    ensures
        alloc_thread_quota_2m_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, alloc_amount) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) { kernel_process_projection_at(krnl, c.current_process->Some_0); }
    if krnl.thr_mp.dom().contains(c.current_thread->Some_0) { kernel_thread_projection_at(krnl, c.current_thread->Some_0); }
}

/// The thread quota wrapper's user-view facts are exactly the thread quota step on `pre`/`post`.
pub(super) proof fn alloc_thread_quota_2m_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, alloc_amount: usize)
    requires
        kernel_u_only_process2thread_quota_2m_changed(pre, post, cpu_id, process_ptr, thread_ptr, alloc_amount as int),
        {
            let cpu = pre.cpu_array[cpu_id as int];
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& !pre.process_map.spec_index(process_ptr).killed
            &&& pre.process_map.spec_index(process_ptr).quota_2m >= alloc_amount as int
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& pre.thread_map.spec_index(thread_ptr).lock_state is Unlocked
            &&& !pre.thread_map.spec_index(thread_ptr).killed
            &&& pre.thread_map.spec_index(thread_ptr).quota_2m + alloc_amount as int <= usize::MAX
            &&& alloc_amount > 0
        },
    ensures
        alloc_thread_quota_2m_step_pre(pre, cpu_id, alloc_amount),
        alloc_thread_quota_2m_step(pre, post, cpu_id, alloc_amount),
{ reveal(alloc_thread_quota_2m_step_pre); }

/// The one step pushed since `before` is the complete successful trace.
pub(super) proof fn alloc_thread_quota_2m_trace_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, alloc_amount: usize)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        alloc_amount > 0,
        alloc_thread_quota_2m_step_pre(pre, cpu_id, alloc_amount),
        alloc_thread_quota_2m_step(pre, post, cpu_id, alloc_amount),
    ensures
        alloc_thread_quota_2m_syscall_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, post, cpu_id, alloc_amount, RetValueType::Success),
{ reveal(alloc_thread_quota_2m_syscall_trace); }

/// A rejected or zero-amount call records no step.
pub(super) proof fn alloc_thread_quota_2m_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, alloc_amount: usize, ret: RetValueType)
    requires
        trace.len() == 0,
        !(ret is Success && alloc_amount > 0),
    ensures
        alloc_thread_quota_2m_syscall_trace(trace, pre, pre, cpu_id, alloc_amount, ret),
{ reveal(alloc_thread_quota_2m_syscall_trace); }
} // verus!
