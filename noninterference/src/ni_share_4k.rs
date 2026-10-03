use vstd::prelude::*;
use crate::*;
use veriflat_map_4k::*;

verus! {
/// A share directory step on a cpu of `a` charges its running thread or its pages peer outside `b`, and
/// moves at most one page from the running thread's container to a child of that container.
pub proof fn share_4k_directory_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        share_4k_directory_step_pre(old_u, cpu_id), share_4k_directory_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(share_4k_directory_step_pre); reveal(share_4k_directory_step); reveal(share_4k_directory_at); reveal(kernel_u_cpu_ownership_wf);
    reveal(kernel_u_container_tree_wf);
}

/// The step of `share_4k_directory_step_lr` preserves isolation.
pub proof fn share_4k_directory_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        share_4k_directory_step_pre(old_u, cpu_id), share_4k_directory_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(share_4k_directory_step_pre); reveal(share_4k_directory_step); reveal(share_4k_directory_pre_at); reveal(share_4k_directory_at);
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf);
}

/// A share leaf step on a cpu of `a` copies an entry into a process of `a` or of its pages peer outside `b`.
pub proof fn share_4k_leaf_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        share_4k_leaf_step_pre(old_u, cpu_id), share_4k_leaf_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_step); reveal(share_4k_leaf_pre_at); reveal(share_4k_leaf_at);
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf);
}

/// The step of `share_4k_leaf_step_lr` preserves isolation. `progress` is the running thread's share and
/// `source` the process whose entry it copies. A source process outside `a` is the pages peer's, and the
/// page it shares is one no process of `b` maps.
pub proof fn share_4k_leaf_step_iso(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, progress: SyscallProgress, source: RwLockProcessPtr, a: RwLockContainerPtr, b: RwLockContainerPtr,
)
    requires
        kernel_u_ownership_wf(old_u), isolated(old_u, a, b), steps_in_domain(old_u, cpu_id, a),
        share_4k_leaf_step_pre(old_u, cpu_id), share_4k_leaf_step(old_u, new_u, cpu_id),
        progress == old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0,
        source == old_u.thread_map[share_4k_objects(old_u, cpu_id).source_thread].owning_proc,
        !in_domain(old_u, a, old_u.process_map[source].owning_container) ==> forall|q: RwLockProcessPtr, v: VAddr|
            #![trigger old_u.process_map[q].pagetable->Some_0.mapping_4k[v]]
            old_u.process_map.dom().contains(q) && in_domain(old_u, b, old_u.process_map[q].owning_container) && old_u.process_map[q].pagetable is Some
            && old_u.process_map[q].pagetable->Some_0.mapping_4k.dom().contains(v)
            ==> old_u.process_map[q].pagetable->Some_0.mapping_4k[v].addr
                != old_u.process_map[source].pagetable->Some_0.mapping_4k[progress->Share4k_source_range.view()[progress->Share4k_shared as int]].addr,
    ensures isolated(new_u, a, b),
{
    reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_step); reveal(share_4k_leaf_pre_at); reveal(share_4k_leaf_at);
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf);
}
} // verus!
