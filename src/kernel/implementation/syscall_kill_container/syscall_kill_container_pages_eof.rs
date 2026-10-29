use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_eof_entry::kill_container_retire_eof_subtree_empty;

verus! {
/// The killer sets `retire_ready` on the marked container `container_ptr` and changes nothing else.
pub(crate) open spec fn kill_container_pages_eof_transition_framing(pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr) -> bool {
    &&& post == (KernelK { ctn_mp: post.ctn_mp, ..pre })
    &&& post.ctn_mp.perms_wf()
    &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr)
    &&& update_ghost_ensures(pre.ctn_mp.spec_index(container_ptr), post.ctn_mp.spec_index(container_ptr),
        ContainerGhost { retire_ready: true, ..pre.ctn_mp.spec_index(container_ptr).view_ghost() })
}

/// The memory invariants hold after the killer sets `retire_ready` on the empty, drained container `container_ptr`.
proof fn kill_container_pages_eof_memory(pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        kill_container_pages_eof_transition_framing(pre, post, container_ptr),
        ({
            let target = pre.ctn_mp.spec_index(container_ptr);
            let ro = target.view_rodata().view();
            &&& target.being_killed()
            &&& target.view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty()
            &&& target.view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& target.view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& target.view().children.view().len() == 0
            &&& pre.allc_4k_mp.spec_index(ro.allocator_ptr_4k).quota.view().value == 0
            &&& pre.allc_2m_mp.spec_index(ro.allocator_ptr_2m).quota.view().value == 0
            &&& pre.allc_1g_mp.spec_index(ro.allocator_ptr_1g).quota.view().value == 0
            &&& forall|i: CpuId| #![trigger pre.allc_4k_mp.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> pre.allc_4k_mp.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& forall|i: CpuId| #![trigger pre.allc_2m_mp.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> pre.allc_2m_mp.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& forall|i: CpuId| #![trigger pre.allc_1g_mp.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> pre.allc_1g_mp.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
        }),
    ensures post.memory_management_inv(),
{
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, container_ptr);
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_page_owner_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { reveal(container_pages_wf); };
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
    assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf); reveal(container_process_allocator_quota_1g_wf);
    };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        assert(pre.ctn_mp.spec_index(container_ptr).view_ghost().subtree_set.view() =~= Set::<RwLockContainerPtr>::empty()) by { broadcast use kill_container_retire_eof_subtree_empty; };
        reveal(container_kill_retire_wf);
    };
}

/// The process invariants hold after the killer sets `retire_ready` on the container `container_ptr`.
proof fn kill_container_pages_eof_process(pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        kill_container_pages_eof_transition_framing(pre, post, container_ptr),
    ensures post.process_management_inv(),
{
    container_kill_mark_wf_at(pre.ctn_mp, pre.prc_mp, container_ptr);
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(pre.ctn_mp.dom().contains(pre.rt_ctn)) by { reveal(container_root_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
        container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp);
    };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
        container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp);
    };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
}

/// Closes `inv()` after the killer sets `retire_ready` on the marked container `container_ptr`, which is empty and whose
/// allocators hold no quota and no cached page: only that container's ghost flag changed.
pub(crate) proof fn kill_container_pages_eof_retire_ready(pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        kill_container_pages_eof_transition_framing(pre, post, container_ptr),
        ({
            let target = pre.ctn_mp.spec_index(container_ptr);
            let ro = target.view_rodata().view();
            &&& target.being_killed()
            &&& target.view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty()
            &&& target.view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& target.view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& target.view().children.view().len() == 0
            &&& pre.allc_4k_mp.spec_index(ro.allocator_ptr_4k).quota.view().value == 0
            &&& pre.allc_2m_mp.spec_index(ro.allocator_ptr_2m).quota.view().value == 0
            &&& pre.allc_1g_mp.spec_index(ro.allocator_ptr_1g).quota.view().value == 0
            &&& forall|i: CpuId| #![trigger pre.allc_4k_mp.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> pre.allc_4k_mp.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& forall|i: CpuId| #![trigger pre.allc_2m_mp.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> pre.allc_2m_mp.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& forall|i: CpuId| #![trigger pre.allc_1g_mp.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> pre.allc_1g_mp.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
        }),
    ensures
        post.inv(),
{
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    kill_container_pages_eof_memory(pre, post, container_ptr); kill_container_pages_eof_process(pre, post, container_ptr);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(container_cpu_wf);
    };
}
} // verus!
