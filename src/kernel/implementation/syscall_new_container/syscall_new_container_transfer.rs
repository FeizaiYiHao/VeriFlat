use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::opaque]
/// Transfers one staged 4K page from the parent container's ownership set to
/// the child container's. Only that page entry and the two containers change.
pub open spec fn staged_4k_page_container_transfer_transition(
    pre: KernelK, post: KernelK, page_ptr: PagePtr,
    staging_thread_ptr: RwLockThreadPtr,
    parent: RwLockContainerPtr, child: RwLockContainerPtr,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    &&& page_ptr_valid(page_ptr)
    &&& parent != child
    &&& pre.ctn_mp.dom().contains(parent)
    &&& pre.ctn_mp.dom().contains(child)
    &&& pre.ctn_mp.spec_index(parent).view().owned_pages.view().contains(page_ptr)
    &&& pre.ctn_mp.spec_index(child).view_rodata().view().parent == Some(parent)
    &&& pre.thr_mp.dom().contains(staging_thread_ptr)
    &&& pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)
    &&& old_page.view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr })
    &&& old_page.view().owning_container == parent
    &&& post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, ..pre })
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& forall|j: PageIndex|
        #![trigger pre.pg_arr.spec_index(j).view().view().state]
        #![trigger post.pg_arr.spec_index(j).view().view().state]
        index_valid(NUM_PAGES, j) ==> {
            &&& post.pg_arr.spec_index(j).view().view().state == pre.pg_arr.spec_index(j).view().view().state
            &&& post.pg_arr.spec_index(j).view().view().mappings() == pre.pg_arr.spec_index(j).view().view().mappings()
            &&& (j != page_index ==> post.pg_arr.spec_index(j).view().view().owning_container == pre.pg_arr.spec_index(j).view().view().owning_container)
        }
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view() == (Page { owning_container: child, ..old_page.view() })
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr|
        #![trigger pre.ctn_mp.spec_index(c)]
        #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let old_container = pre.ctn_mp.spec_index(c);
            let new_container = post.ctn_mp.spec_index(c);
            &&& post.ctn_mp.view().spec_index(c).is_init() == pre.ctn_mp.view().spec_index(c).is_init()
            &&& post.ctn_mp.view().spec_index(c).addr() == pre.ctn_mp.view().spec_index(c).addr()
            &&& (c != parent && c != child ==> new_container == old_container)
            &&& (c == parent || c == child ==> {
                &&& new_container.is_init() == old_container.is_init()
                &&& new_container.view_rodata() == old_container.view_rodata()
                &&& new_container.view_ghost() == old_container.view_ghost()
                &&& new_container.locking_thread() == old_container.locking_thread()
                &&& new_container.being_killed() == old_container.being_killed()
                &&& new_container.view() == (Container {
                    owned_pages: Ghost(if c == parent {
                        old_container.view().owned_pages.view().remove(page_ptr)
                    } else {
                        old_container.view().owned_pages.view().insert(page_ptr)
                    }),
                    ..old_container.view()
                })
            })
        }
}

#[verifier::spinoff_prover]
proof fn staged_4k_page_container_transfer_eof_process_management_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr,
    staging_thread_ptr: RwLockThreadPtr,
    parent: RwLockContainerPtr, child: RwLockContainerPtr,
)
    requires
        pre.inv(),
        staged_4k_page_container_transfer_transition(pre, post, page_ptr, staging_thread_ptr, parent, child),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(staged_4k_page_container_transfer_transition);
    assert(post.process_management_inv()) by {
        assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by {
            reveal(container_perms_wf); reveal(LinkedList::wf_value_list);
            reveal(container_root_wf); reveal(container_children_parent_wf); reveal(containers_linkedlist_wf);
            reveal(container_children_depth_wf); reveal(container_subtree_set_wf);
            reveal(container_uppertree_seq_wf); reveal(container_subtree_set_exclusive);
        };
        assert(post.ctn_mp.spec_index(post.rt_ctn).view().root_process_in_processes()) by { reveal(container_root_wf); };
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); };
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_thread_wf); reveal(container_process_wf); reveal(process_thread_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf); };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
        assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(container_process_wf); reveal(process_pcid_allocator_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
    };
}

pub(super) proof fn staged_4k_page_container_transfer_eof(
    pre: KernelK, post: KernelK, page_ptr: PagePtr,
    staging_thread_ptr: RwLockThreadPtr,
    parent: RwLockContainerPtr, child: RwLockContainerPtr,
)
    requires
        pre.inv(),
        staged_4k_page_container_transfer_transition(pre, post, page_ptr, staging_thread_ptr, parent, child),
        post.pg_arr.inv(),
    ensures post.inv(),
{
    reveal(staged_4k_page_container_transfer_transition);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); };
    assert(post.ctn_mp.perms_wf()) by { reveal(container_perms_wf); };
    assert(container_tree_fields_wf(post.ctn_mp)) by { reveal(container_tree_fields_wf); reveal(container_perms_wf); };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf); };
        assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_page_owner_wf); };
        assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
        assert(hugepage_1g_wf(post.pg_arr)) by { reveal(hugepage_1g_wf); };
        assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
            assert(post.pg_arr.spec_index(page_index).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr })) by { reveal(staged_4k_page_container_transfer_transition); };
            assert(!pre.pg_arr.spec_index(page_index).view().view().is_mapped() && !post.pg_arr.spec_index(page_index).view().view().is_mapped());
            reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf);
        };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by {
            reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(container_page_owner_wf);
            reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf);
            reveal(mapped_1g_page_pagetable_wf); reveal(process_pagetable_match);
        };
        assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { reveal(container_pages_wf); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { reveal(process_pages_wf); };
        assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
        assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
        assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by {
            assert(post.pg_arr.spec_index(page_index).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr })) by { reveal(staged_4k_page_container_transfer_transition); };
            reveal(thread_staged_pages_4k_wf);
        };
        assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
        assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by {
            assert(post.pg_arr.spec_index(page_index).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr })) by { reveal(staged_4k_page_container_transfer_transition); };
            reveal(thread_staged_pages_1g_wf);
        };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
        assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf); reveal(container_process_allocator_quota_1g_wf); };
        assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
    };
    staged_4k_page_container_transfer_eof_process_management_inv(pre, post, page_ptr, staging_thread_ptr, parent, child);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        reveal(container_cpu_wf);
    };
    assert(iommu_root_table_process_wf(&post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(&post.irt, post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
}
}
