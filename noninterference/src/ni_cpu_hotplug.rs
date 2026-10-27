use vstd::prelude::*;
use crate::*;
use veriflat_syscall_cpu_hotplug::syscall_cpu_hotplug::{cpu_offline_check_spec::*, syscall_cpu_hotplug_spec::*};

verus! {
/// Setting a request bit in the container of a cpu of `a` leaves the view of `b` unchanged.
pub proof fn cpu_offline_request_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_offline_request_step_pre(old_u, cpu_id, target),
        cpu_offline_request_step(old_u, new_u, cpu_id, target),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_cpu_offline_request_changed); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `cpu_offline_request_step_lr` preserves isolation.
pub proof fn cpu_offline_request_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_offline_request_step_pre(old_u, cpu_id, target),
        cpu_offline_request_step(old_u, new_u, cpu_id, target),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_cpu_offline_request_changed); reveal(kernel_u_cpu_ownership_wf); }

/// Write-locking a cpu of `a` for the offline recheck changes only that cpu, which `a` owns.
pub proof fn cpu_offline_check_hold_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_offline_check_hold_step_pre(old_u, cpu_id),
        cpu_offline_check_hold_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(cpu_offline_check_hold_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `cpu_offline_check_hold_step_lr` preserves isolation.
pub proof fn cpu_offline_check_hold_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_offline_check_hold_step_pre(old_u, cpu_id),
        cpu_offline_check_hold_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(cpu_offline_check_hold_step); }

/// Unlocking a cpu of `a` after a recheck that continues changes only that cpu, which `a` owns.
pub proof fn cpu_offline_check_release_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_offline_check_release_step_pre(old_u, cpu_id),
        cpu_offline_check_release_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(cpu_offline_check_release_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `cpu_offline_check_release_step_lr` preserves isolation.
pub proof fn cpu_offline_check_release_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_offline_check_release_step_pre(old_u, cpu_id),
        cpu_offline_check_release_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(cpu_offline_check_release_step); }

/// A cpu of `a` going Off, requeueing its thread in its own container, leaves the view of `b` unchanged.
pub proof fn cpu_offline_check_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_offline_check_step_pre(old_u, cpu_id),
        cpu_offline_check_step(old_u, new_u, cpu_id, regs, flushed_default_pcid),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_cpu_went_off_changed); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `cpu_offline_check_step_lr` preserves isolation.
pub proof fn cpu_offline_check_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_offline_check_step_pre(old_u, cpu_id),
        cpu_offline_check_step(old_u, new_u, cpu_id, regs, flushed_default_pcid),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_cpu_went_off_changed); reveal(kernel_u_cpu_ownership_wf); }

/// Publishing Idle on an Off cpu of the container of a cpu of `a` leaves the view of `b` unchanged.
pub proof fn cpu_online_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_online_step_pre(old_u, cpu_id, target),
        cpu_online_step(old_u, new_u, cpu_id, target),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_cpu_online_changed); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `cpu_online_step_lr` preserves isolation.
pub proof fn cpu_online_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_online_step_pre(old_u, cpu_id, target),
        cpu_online_step(old_u, new_u, cpu_id, target),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_cpu_online_changed); }

/// Setting a request bit in a direct child of the container of a cpu of `a`, which lies in `a`, leaves the view
/// of `b` unchanged.
pub proof fn cpu_offline_request_child_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_offline_request_child_step_pre(old_u, cpu_id, target),
        cpu_offline_request_child_step(old_u, new_u, cpu_id, target),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_cpu_offline_request_changed); reveal(kernel_u_cpu_ownership_wf); assert(in_domain(old_u, a, old_u.cpu_array[target as int].owning_container)) by { reveal(kernel_u_container_tree_wf); }; }

/// The step of `cpu_offline_request_child_step_lr` preserves isolation.
pub proof fn cpu_offline_request_child_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_offline_request_child_step_pre(old_u, cpu_id, target),
        cpu_offline_request_child_step(old_u, new_u, cpu_id, target),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_cpu_offline_request_changed); reveal(kernel_u_cpu_ownership_wf); }

/// Publishing Idle on an Off cpu of a direct child of the container of a cpu of `a`, which lies in `a`, leaves
/// the view of `b` unchanged.
pub proof fn cpu_online_child_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_online_child_step_pre(old_u, cpu_id, target),
        cpu_online_child_step(old_u, new_u, cpu_id, target),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_cpu_online_changed); reveal(kernel_u_cpu_ownership_wf); assert(in_domain(old_u, a, old_u.cpu_array[target as int].owning_container)) by { reveal(kernel_u_container_tree_wf); }; }

/// The step of `cpu_online_child_step_lr` preserves isolation.
pub proof fn cpu_online_child_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, target: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        cpu_online_child_step_pre(old_u, cpu_id, target),
        cpu_online_child_step(old_u, new_u, cpu_id, target),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_cpu_online_changed); }

/// The offline-request result of a cpu of `b` reads only the view of `b`: its own cpu and, when `target`
/// belongs to its container, that cpu; a `target` outside the view is rejected in both states.
pub proof fn cpu_offline_request_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, target: CpuId, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures cpu_offline_request_syscall_result(u1, cpu_id, target) == cpu_offline_request_syscall_result(u2, cpu_id, target),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        &&& v1.cpus[cpu_id as int] == Some(u1.cpu_array[cpu_id as int])
        &&& v1.cpus[cpu_id as int] == v2.cpus[cpu_id as int]
        &&& index_valid(NUM_CPUS, target) ==> v1.cpus[target as int] == v2.cpus[target as int]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}

/// The online result of a cpu of `b` reads only the view of `b`, as `cpu_offline_request_syscall_result_oc`.
pub proof fn cpu_online_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, target: CpuId, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures cpu_online_syscall_result(u1, cpu_id, target) == cpu_online_syscall_result(u2, cpu_id, target),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        &&& v1.cpus[cpu_id as int] == Some(u1.cpu_array[cpu_id as int])
        &&& v1.cpus[cpu_id as int] == v2.cpus[cpu_id as int]
        &&& index_valid(NUM_CPUS, target) ==> v1.cpus[target as int] == v2.cpus[target as int]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
}

/// The child offline-request result of a cpu of `b` reads only the view of `b`: its own cpu, its container, and
/// `target` when that cpu lies in the domain. Every child of the caller's container lies in the domain, so a
/// `target` outside the view is rejected in both states.
pub proof fn cpu_offline_request_child_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, child: usize, target: CpuId, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        u1.container_map.dom().contains(b),
        steps_in_domain(u1, cpu_id, b),
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures cpu_offline_request_child_syscall_result(u1, cpu_id, child, target) == cpu_offline_request_child_syscall_result(u2, cpu_id, child, target),
{
    let caller = u1.cpu_array[cpu_id as int].owning_container;
    let children = u1.container_map[caller].children;
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        &&& v1.cpus[cpu_id as int] == Some(u1.cpu_array[cpu_id as int])
        &&& v1.cpus[cpu_id as int] == v2.cpus[cpu_id as int]
        &&& index_valid(NUM_CPUS, target) ==> v1.cpus[target as int] == v2.cpus[target as int]
        &&& v1.containers.dom().contains(caller)
        &&& v1.containers[caller] == v2.containers[caller]
        &&& u1.cpu_array[cpu_id as int].state is Running ==> {
            let p = u1.cpu_array[cpu_id as int].current_process->Some_0;
            &&& u1.cpu_array[cpu_id as int].current_process is Some
            &&& v1.processes.dom().contains(p)
            &&& v1.processes[p] == v2.processes[p]
        }
    }) by { reveal(kernel_u_cpu_ownership_wf); };
    if child < children.len() { assert(domain_view(u1, b).containers.dom().contains(children[child as int])) by { reveal(kernel_u_container_tree_wf); broadcast use vstd::seq::Seq::lemma_index_contains; }; }
}

/// The child online result of a cpu of `b` reads only the view of `b`, as
/// `cpu_offline_request_child_syscall_result_oc`.
pub proof fn cpu_online_child_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, child: usize, target: CpuId, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        u1.container_map.dom().contains(b),
        steps_in_domain(u1, cpu_id, b),
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures cpu_online_child_syscall_result(u1, cpu_id, child, target) == cpu_online_child_syscall_result(u2, cpu_id, child, target),
{
    let caller = u1.cpu_array[cpu_id as int].owning_container;
    let children = u1.container_map[caller].children;
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        &&& v1.cpus[cpu_id as int] == Some(u1.cpu_array[cpu_id as int])
        &&& v1.cpus[cpu_id as int] == v2.cpus[cpu_id as int]
        &&& index_valid(NUM_CPUS, target) ==> v1.cpus[target as int] == v2.cpus[target as int]
        &&& v1.containers.dom().contains(caller)
        &&& v1.containers[caller] == v2.containers[caller]
        &&& u1.cpu_array[cpu_id as int].state is Running ==> {
            let p = u1.cpu_array[cpu_id as int].current_process->Some_0;
            &&& u1.cpu_array[cpu_id as int].current_process is Some
            &&& v1.processes.dom().contains(p)
            &&& v1.processes[p] == v2.processes[p]
        }
    }) by { reveal(kernel_u_cpu_ownership_wf); };
    if child < children.len() { assert(domain_view(u1, b).containers.dom().contains(children[child as int])) by { reveal(kernel_u_container_tree_wf); broadcast use vstd::seq::Seq::lemma_index_contains; }; }
}

/// The offline-check result of a cpu of `b` reads only the view of `b`: the cpu, its container's request
/// bits, and its current process and thread, which that container owns.
pub proof fn cpu_offline_check_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        kernel_u_cpu_current_pair_wf(u1),
        steps_in_domain(u1, cpu_id, b),
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures cpu_offline_check_result(u1, cpu_id) == cpu_offline_check_result(u2, cpu_id),
{
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        let cpu = u1.cpu_array[cpu_id as int];
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.containers.dom().contains(cpu.owning_container)
        &&& v1.containers[cpu.owning_container] == v2.containers[cpu.owning_container]
        &&& cpu.current_process is Some ==> {
            &&& v1.processes.dom().contains(cpu.current_process->Some_0)
            &&& v1.processes[cpu.current_process->Some_0] == v2.processes[cpu.current_process->Some_0]
            &&& v1.threads.dom().contains(cpu.current_thread->Some_0)
            &&& v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
        }
    }) by { reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_cpu_current_pair_wf); };
}
} // verus!
