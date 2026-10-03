use vstd::prelude::*;
use crate::*;
use veriflat_map_4k::*;
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;

verus! {
/// Entering mmap on a cpu of `a` locks only objects of `a`.
pub proof fn mmap_4k_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        mmap_4k_enter_step_pre(old_u, cpu_id, range), mmap_4k_enter_step(old_u, new_u, cpu_id, range),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `mmap_4k_enter_step_lr` preserves isolation.
pub proof fn mmap_4k_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, range: VaRange4K, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        mmap_4k_enter_step_pre(old_u, cpu_id, range), mmap_4k_enter_step(old_u, new_u, cpu_id, range),
    ensures isolated(new_u, a, b),
{ reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); }

/// An mmap directory step on a cpu of `a` changes only its running thread.
pub proof fn mmap_4k_directory_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        mmap_4k_directory_step_pre(old_u, cpu_id), mmap_4k_directory_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `mmap_4k_directory_step_lr` preserves isolation.
pub proof fn mmap_4k_directory_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        mmap_4k_directory_step_pre(old_u, cpu_id), mmap_4k_directory_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); }

/// An mmap leaf on a cpu of `a` maps a page that no process maps, into a process of `a`.
pub proof fn mmap_4k_leaf_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        mmap_4k_leaf_step_pre(old_u, cpu_id), mmap_4k_leaf_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `mmap_4k_leaf_step_lr` preserves isolation.
pub proof fn mmap_4k_leaf_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        mmap_4k_leaf_step_pre(old_u, cpu_id), mmap_4k_leaf_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// Exiting mmap on a cpu of `a` unlocks only objects of `a`.
pub proof fn mmap_4k_exit_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        mmap_4k_exit_step_pre(old_u, cpu_id), mmap_4k_exit_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The step of `mmap_4k_exit_step_lr` preserves isolation.
pub proof fn mmap_4k_exit_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        mmap_4k_exit_step_pre(old_u, cpu_id), mmap_4k_exit_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); }

/// The 4K mmap result of a running cpu of `b` reads only the view of `b`.
pub proof fn mmap_4k_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, va: VAddr, range: usize, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1), steps_in_domain(u1, cpu_id, b), u1.cpu_array[cpu_id as int].state is Running,
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures mmap_4k_syscall_result(u1, cpu_id, va, range) == mmap_4k_syscall_result(u2, cpu_id, va, range),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        let thread = u1.thread_map[cpu.current_thread->Some_0];
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.threads.dom().contains(cpu.current_thread->Some_0) && v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
        &&& v1.processes.dom().contains(thread.owning_proc) && v1.processes[thread.owning_proc] == v2.processes[thread.owning_proc]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}
} // verus!
