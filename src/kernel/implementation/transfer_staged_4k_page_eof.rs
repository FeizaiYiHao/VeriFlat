use vstd::prelude::*;
use crate::*;

verus! {
/// Transfers one staged 4K page from the parent container's ownership set to
/// the child container's. Only that page entry and the two containers change.
#[verifier::opaque]
pub open spec fn transfer_staged_4k_page_to_child_container_eof_transition_framing(pre: KernelK, post: KernelK, page_ptr: PagePtr, staging_thread_ptr: RwLockThreadPtr, parent: RwLockContainerPtr, child: RwLockContainerPtr) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
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
                &&& new_container.killer_info() == old_container.killer_info()
                &&& new_container.view() == (Container {
                    owned_pages: Ghost(if c == parent { old_container.view().owned_pages.view().remove(page_ptr) } else { old_container.view().owned_pages.view().insert(page_ptr) }),
                    ..old_container.view()
                })
            })
        }
}

proof fn staged_4k_page_container_transfer_eof_container_tree(pre: KernelK, post: KernelK, page_ptr: PagePtr, staging_thread_ptr: RwLockThreadPtr, parent: RwLockContainerPtr, child: RwLockContainerPtr)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        parent != child,
        pre.ctn_mp.dom().contains(parent),
        pre.ctn_mp.dom().contains(child),
        pre.ctn_mp.spec_index(parent).view().owned_pages.view().contains(page_ptr),
        pre.ctn_mp.spec_index(child).view_rodata().view().parent == Some(parent),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == parent,
        transfer_staged_4k_page_to_child_container_eof_transition_framing(pre, post, page_ptr, staging_thread_ptr, parent, child),
        post.subsystems_inv(),
    ensures
        container_tree_wf(post.rt_ctn, post.ctn_mp),
        post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process),
{
    hide(Seq::contains);
    reveal(transfer_staged_4k_page_to_child_container_eof_transition_framing);
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by {
        reveal(container_perms_wf); reveal(LinkedList::wf_value_list); reveal(container_root_wf); reveal(container_children_parent_wf); reveal(containers_linkedlist_wf);
        reveal(container_children_depth_wf); reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_subtree_set_exclusive);
    };
    assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
}

proof fn staged_4k_page_container_transfer_eof_process_management_inv(pre: KernelK, post: KernelK, page_ptr: PagePtr, staging_thread_ptr: RwLockThreadPtr, parent: RwLockContainerPtr, child: RwLockContainerPtr)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        parent != child,
        pre.ctn_mp.dom().contains(parent),
        pre.ctn_mp.dom().contains(child),
        pre.ctn_mp.spec_index(parent).view().owned_pages.view().contains(page_ptr),
        pre.ctn_mp.spec_index(child).view_rodata().view().parent == Some(parent),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == parent,
        transfer_staged_4k_page_to_child_container_eof_transition_framing(pre, post, page_ptr, staging_thread_ptr, parent, child),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    hide(Seq::contains);
    reveal(transfer_staged_4k_page_to_child_container_eof_transition_framing);
    staged_4k_page_container_transfer_eof_container_tree(pre, post, page_ptr, staging_thread_ptr, parent, child);
    assert(post.process_management_inv()) by {
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); };
        assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
        assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
        assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { container_cpu_offline_flags_wf_preserved_for_flags_owner_eq(pre.ctn_mp, post.ctn_mp, pre.cpu_offline_mp, post.cpu_offline_mp); };
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { container_cpu_wf_preserved_for_container_cpu_fields_eq(pre.ctn_mp, post.ctn_mp, post.cpu_set_mp, post.cpu_arr); reveal(container_thread_wf); reveal(container_process_wf); reveal(process_thread_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
            reveal(container_endpoint_wf);
            reveal(thread_endpoint_ref_counter_wf);
            reveal(thread_endpoint_queue_wf);
            container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp);
        };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
        assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(container_process_wf); reveal(process_pcid_allocator_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { reveal(container_thread_wf); reveal(container_scheduler_wf); container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
    };
}

/// Only the two containers' owned pages change, so every retire-ready container keeps its marked, empty state and its allocators.
proof fn staged_4k_page_container_transfer_eof_kill_retire_wf(pre: KernelK, post: KernelK, page_ptr: PagePtr, staging_thread_ptr: RwLockThreadPtr, parent: RwLockContainerPtr, child: RwLockContainerPtr)
    requires
        container_kill_retire_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        transfer_staged_4k_page_to_child_container_eof_transition_framing(pre, post, page_ptr, staging_thread_ptr, parent, child),
    ensures
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{ reveal(transfer_staged_4k_page_to_child_container_eof_transition_framing); reveal(container_kill_retire_wf); }

/// The transferred page keeps its staging thread, which write-holds the live child container that now owns the page;
/// every other page keeps its owner, which stays in the container map.
proof fn staged_4k_page_container_transfer_eof_page_object_owner(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, staging_thread_ptr: RwLockThreadPtr, parent: RwLockContainerPtr, child: RwLockContainerPtr,
)
    requires
        page_object_owner_wf(pre.pg_arr, pre.ctn_mp, pre.thr_mp),
        container_page_owner_wf(pre.ctn_mp, pre.pg_arr),
        page_array_wf(pre.pg_arr),
        page_ptr_valid(page_ptr),
        parent != child,
        pre.ctn_mp.dom().contains(parent),
        pre.ctn_mp.dom().contains(child),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == parent,
        transfer_staged_4k_page_to_child_container_eof_transition_framing(pre, post, page_ptr, staging_thread_ptr, parent, child),
        pre.ctn_mp.spec_index(child).locking_thread() is Write,
        pre.thr_mp.spec_index(staging_thread_ptr).locking_thread() is Write,
        pre.ctn_mp.spec_index(child).locking_thread()->Write_thread_id == pre.thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_thread_id,
        !pre.ctn_mp.spec_index(child).being_killed(),
    ensures page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp),
{
    reveal(transfer_staged_4k_page_to_child_container_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_array_wf_at(pre.pg_arr, page_ptr2page_index(page_ptr)); reveal(page_object_owner_wf); reveal(container_page_owner_wf);
}

pub(super) proof fn staged_4k_page_container_transfer_eof_inv(pre: KernelK, post: KernelK, page_ptr: PagePtr, staging_thread_ptr: RwLockThreadPtr, parent: RwLockContainerPtr, child: RwLockContainerPtr)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        parent != child,
        pre.ctn_mp.dom().contains(parent),
        pre.ctn_mp.dom().contains(child),
        pre.ctn_mp.spec_index(parent).view().owned_pages.view().contains(page_ptr),
        pre.ctn_mp.spec_index(child).view_rodata().view().parent == Some(parent),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == parent,
        transfer_staged_4k_page_to_child_container_eof_transition_framing(pre, post, page_ptr, staging_thread_ptr, parent, child),
        post.pg_arr.inv(),
        pre.ctn_mp.spec_index(child).locking_thread() is Write,
        pre.thr_mp.spec_index(staging_thread_ptr).locking_thread() is Write,
        pre.ctn_mp.spec_index(child).locking_thread()->Write_thread_id == pre.thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_thread_id,
        !pre.ctn_mp.spec_index(child).being_killed(),
    ensures
        post.inv(),
        post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, ..pre }),
        post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_ptr2page_index(page_ptr)),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state,
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child,
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
            pre.ctn_mp.dom().contains(c) && c != parent && c != child ==> post.ctn_mp.spec_index(c) == pre.ctn_mp.spec_index(c),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
            c == parent || c == child ==> {
                &&& post.ctn_mp.spec_index(c).is_init() == pre.ctn_mp.spec_index(c).is_init()
                &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
                &&& post.ctn_mp.spec_index(c).view_ghost() == pre.ctn_mp.spec_index(c).view_ghost()
                &&& post.ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
                &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
                &&& post.ctn_mp.spec_index(c).killer_info() == pre.ctn_mp.spec_index(c).killer_info()
                &&& post.ctn_mp.spec_index(c).view() == (Container { owned_pages: post.ctn_mp.spec_index(c).view().owned_pages, ..pre.ctn_mp.spec_index(c).view() })
            },
        post.ctn_mp.spec_index(parent).view().owned_pages.view() == pre.ctn_mp.spec_index(parent).view().owned_pages.view().remove(page_ptr),
        post.ctn_mp.spec_index(child).view().owned_pages.view() == pre.ctn_mp.spec_index(child).view().owned_pages.view().insert(page_ptr),
{
    reveal(transfer_staged_4k_page_to_child_container_eof_transition_framing);
    assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); reveal(Page::mappings_va_valid); };
    assert(container_tree_fields_wf(post.ctn_mp)) by { reveal(container_tree_fields_wf); reveal(container_perms_wf); };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
            allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
            allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
        };
        assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_page_owner_wf); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        staged_4k_page_container_transfer_eof_page_object_owner(pre, post, page_ptr, staging_thread_ptr, parent, child);
        assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); reveal(pagetable_lower_wf);
        };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
        assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
        assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf); reveal(container_process_allocator_quota_1g_wf);
        };
        assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp); };
        staged_4k_page_container_transfer_eof_kill_retire_wf(pre, post, page_ptr, staging_thread_ptr, parent, child);
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(page_ptr)); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(page_ptr)); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_ptr2page_index(page_ptr)); };
    };
    staged_4k_page_container_transfer_eof_process_management_inv(pre, post, page_ptr, staging_thread_ptr, parent, child);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(container_cpu_wf);
    };
}
}
