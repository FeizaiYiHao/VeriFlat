use vstd::prelude::*;
use crate::*;
use veriflat_map_4k::*;

verus! {
/// A share directory step on a cpu of `a` charges its running thread or its pages peer outside `b`, and
/// moves at most one page from the running thread's container to a child of that container.
pub proof fn share_4k_directory_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        share_4k_directory_step_pre(old_u, cpu_id),
        share_4k_directory_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(share_4k_directory_step_pre); reveal(share_4k_directory_step); reveal(share_4k_directory_at); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf); }

/// The step of `share_4k_directory_step_lr` preserves isolation.
pub proof fn share_4k_directory_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        share_4k_directory_step_pre(old_u, cpu_id),
        share_4k_directory_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(share_4k_directory_step_pre); reveal(share_4k_directory_step); reveal(share_4k_directory_pre_at); reveal(share_4k_directory_at); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf); }

/// A share leaf step on a cpu of `a` copies an entry into a process of `a` or of its pages peer outside `b`.
pub proof fn share_4k_leaf_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        share_4k_leaf_step_pre(old_u, cpu_id),
        share_4k_leaf_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_step); reveal(share_4k_leaf_pre_at); reveal(share_4k_leaf_at); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf); }

/// The step of `share_4k_leaf_step_lr` preserves isolation. `progress` is the running thread's share and
/// `source` the process whose entry it copies. A source process outside `a` is the pages peer's, and the
/// page it shares is one no process of `b` maps in its page table or IOMMU table.
pub proof fn share_4k_leaf_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, progress: SyscallProgress, source: RwLockProcessPtr, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        share_4k_leaf_step_pre(old_u, cpu_id),
        share_4k_leaf_step(old_u, new_u, cpu_id),
        progress == old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0,
        source == old_u.thread_map[share_4k_objects(old_u, cpu_id).source_thread].owning_proc,
        !in_domain(old_u, a, old_u.process_map[source].owning_container) ==> {
            let shared = old_u.process_map[source].pagetable->Some_0.mapping_4k[progress->Share4k_source_range.view()[progress->Share4k_shared as int]].addr;
            &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[q].pagetable->Some_0.mapping_4k[v]]
                old_u.process_map.dom().contains(q) && in_domain(old_u, b, old_u.process_map[q].owning_container) && old_u.process_map[q].pagetable is Some && old_u.process_map[q].pagetable->Some_0.mapping_4k.dom().contains(v)
                    ==> old_u.process_map[q].pagetable->Some_0.mapping_4k[v].addr != shared
            &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[q].iommu_table->Some_0.mapping_4k[v]]
                old_u.process_map.dom().contains(q) && in_domain(old_u, b, old_u.process_map[q].owning_container) && old_u.process_map[q].iommu_table is Some && old_u.process_map[q].iommu_table->Some_0.mapping_4k.dom().contains(v)
                    ==> old_u.process_map[q].iommu_table->Some_0.mapping_4k[v].addr != shared
        },
    ensures isolated(new_u, a, b),
{
    let target = share_4k_objects(old_u, cpu_id).target;
    let source_va = progress->Share4k_source_range.view()[progress->Share4k_shared as int];
    let target_va = progress->Share4k_target_range.view()[progress->Share4k_shared as int];
    let entry = old_u.process_map[source].pagetable->Some_0.mapping_4k[source_va];
    assert(old_u.process_map.dom().contains(source) && old_u.process_map[source].pagetable is Some && old_u.process_map[source].pagetable->Some_0.mapping_4k.dom().contains(source_va)
        && old_u.process_map.dom().contains(target) && old_u.process_map[target].pagetable is Some && old_u.thread_map.dom().contains(old_u.cpu_array[cpu_id as int].current_thread->Some_0))
        by { reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_pre_at); }
    assert(!in_domain(old_u, b, old_u.process_map[target].owning_container)) by {
        reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_pre_at); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_container_tree_wf);
    }
    assert(forall|q: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[q].pagetable->Some_0.mapping_4k[v]]
        old_u.process_map.dom().contains(q) && in_domain(old_u, b, old_u.process_map[q].owning_container) && old_u.process_map[q].pagetable is Some && old_u.process_map[q].pagetable->Some_0.mapping_4k.dom().contains(v)
            ==> old_u.process_map[q].pagetable->Some_0.mapping_4k[v].addr != entry.addr);
    assert(forall|q: RwLockProcessPtr, v: VAddr| #![trigger old_u.process_map[q].iommu_table->Some_0.mapping_4k[v]]
        old_u.process_map.dom().contains(q) && in_domain(old_u, b, old_u.process_map[q].owning_container) && old_u.process_map[q].iommu_table is Some && old_u.process_map[q].iommu_table->Some_0.mapping_4k.dom().contains(v)
            ==> old_u.process_map[q].iommu_table->Some_0.mapping_4k[v].addr != entry.addr);
    assert({
        &&& new_u.container_map == old_u.container_map && new_u.endpoint_map == old_u.endpoint_map
        &&& new_u.process_map.dom() =~= old_u.process_map.dom() && new_u.thread_map.dom() =~= old_u.thread_map.dom()
        &&& new_u.process_map[target].pagetable->Some_0.mapping_4k == old_u.process_map[target].pagetable->Some_0.mapping_4k.insert(target_va, entry)
        &&& forall|p: RwLockProcessPtr| #![trigger new_u.process_map[p]] {
            &&& new_u.process_map[p].owning_container == old_u.process_map[p].owning_container && new_u.process_map[p].iommu_table == old_u.process_map[p].iommu_table
            &&& (new_u.process_map[p].pagetable is Some) == (old_u.process_map[p].pagetable is Some)
            &&& new_u.process_map[p].pagetable->Some_0.mapping_2m == old_u.process_map[p].pagetable->Some_0.mapping_2m
            &&& new_u.process_map[p].pagetable->Some_0.mapping_1g == old_u.process_map[p].pagetable->Some_0.mapping_1g
            &&& p != target ==> new_u.process_map[p].pagetable == old_u.process_map[p].pagetable
        }
        &&& forall|t: RwLockThreadPtr| #![trigger new_u.thread_map[t]]
            new_u.thread_map[t].owning_container == old_u.thread_map[t].owning_container && new_u.thread_map[t].state == old_u.thread_map[t].state
    }) by { reveal(share_4k_leaf_step); reveal(share_4k_leaf_at); }
}
} // verus!
