use vstd::prelude::*;
use crate::*;

verus! {
/// The head page of the 4K global pool `src_allocator` of `src`, held in list node `node`, moves to the head of the 4K
/// global pool `dst_allocator` of `dst`: the page's allocator and owner, the two pools, their free page counts and
/// quotas, and the two containers' owned pages change; nothing else does.
#[verifier::opaque]
pub(super) open spec fn kill_container_move_free_page_4k_eof_transition_framing(
    pre: KernelK, post: KernelK, src: RwLockContainerPtr, dst: RwLockContainerPtr, src_allocator: RwLockPageAllocatorPtr, dst_allocator: RwLockPageAllocatorPtr,
    page_ptr: PagePtr, node: usize,
) -> bool {
    let index = page_ptr2page_index(page_ptr);
    let old_page = pre.pg_arr.spec_index(index).view();
    let new_page = post.pg_arr.spec_index(index).view();
    let old_src = pre.allc_4k_mp.spec_index(src_allocator);
    let new_src = post.allc_4k_mp.spec_index(src_allocator);
    let old_dst = pre.allc_4k_mp.spec_index(dst_allocator);
    let new_dst = post.allc_4k_mp.spec_index(dst_allocator);
    &&& post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, index)
    &&& new_page.view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(dst_allocator), state: FreePageAllocatorState::GlobalList }, owning_container: dst, ..old_page.view() })
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr|
        #![trigger pre.ctn_mp.spec_index(c)]
        #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let old_container = pre.ctn_mp.spec_index(c);
            let new_container = post.ctn_mp.spec_index(c);
            &&& post.ctn_mp.view().spec_index(c).is_init() == pre.ctn_mp.view().spec_index(c).is_init()
            &&& post.ctn_mp.view().spec_index(c).addr() == pre.ctn_mp.view().spec_index(c).addr()
            &&& (c != src && c != dst ==> new_container == old_container)
            &&& (c == src || c == dst ==> {
                &&& new_container.is_init() == old_container.is_init()
                &&& new_container.view_rodata() == old_container.view_rodata()
                &&& new_container.view_ghost() == old_container.view_ghost()
                &&& new_container.locking_thread() == old_container.locking_thread()
                &&& new_container.being_killed() == old_container.being_killed()
                &&& new_container.killer_info() == old_container.killer_info()
                &&& new_container.view() == (Container {
                    owned_pages: Ghost(if c == src { old_container.view().owned_pages.view().remove(page_ptr) } else { old_container.view().owned_pages.view().insert(page_ptr) }),
                    ..old_container.view()
                })
            })
        }
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& forall|a: RwLockPageAllocatorPtr|
        #![trigger post.allc_4k_mp.spec_index(a)]
        pre.allc_4k_mp.dom().contains(a) && a != src_allocator && a != dst_allocator ==> post.allc_4k_mp.spec_index(a) == pre.allc_4k_mp.spec_index(a)
    &&& new_src == (PageAllocator { global_pool: new_src.global_pool, quota: new_src.quota, total_free_pages: new_src.total_free_pages, ..old_src })
    &&& old_src.global_pool.view().map().dom().contains(node)
    &&& old_src.global_pool.view().map().spec_index(node) == page_ptr
    &&& new_src.global_pool.view().view() == old_src.global_pool.view().view().skip(1)
    &&& new_src.global_pool.view().map() == old_src.global_pool.view().map().remove(node)
    &&& new_src.global_pool.is_init()
    &&& new_src.global_pool.lock_id() == old_src.global_pool.lock_id()
    &&& new_src.global_pool.locking_thread() == old_src.global_pool.locking_thread()
    &&& new_src.global_pool.being_killed() == old_src.global_pool.being_killed()
    &&& new_src.quota.view() == (AllocatorQuota { value: (old_src.quota.view().value - 1) as usize, ..old_src.quota.view() })
    &&& new_src.quota.is_init()
    &&& new_src.quota.lock_id() == old_src.quota.lock_id()
    &&& new_src.quota.locking_thread() == old_src.quota.locking_thread()
    &&& new_src.quota.being_killed() == old_src.quota.being_killed()
    &&& new_src.total_free_pages.view() == old_src.total_free_pages.view() - 1
    &&& new_dst == (PageAllocator { global_pool: new_dst.global_pool, quota: new_dst.quota, total_free_pages: new_dst.total_free_pages, ..old_dst })
    &&& !old_dst.global_pool.view().map().dom().contains(node)
    &&& new_dst.global_pool.view().view() == old_dst.global_pool.view().view().insert(0, page_ptr)
    &&& new_dst.global_pool.view().map() == old_dst.global_pool.view().map().insert(node, page_ptr)
    &&& new_dst.global_pool.is_init()
    &&& new_dst.global_pool.lock_id() == old_dst.global_pool.lock_id()
    &&& new_dst.global_pool.locking_thread() == old_dst.global_pool.locking_thread()
    &&& new_dst.global_pool.being_killed() == old_dst.global_pool.being_killed()
    &&& new_dst.quota.view() == (AllocatorQuota { value: (old_dst.quota.view().value + 1) as usize, ..old_dst.quota.view() })
    &&& new_dst.quota.is_init()
    &&& new_dst.quota.lock_id() == old_dst.quota.lock_id()
    &&& new_dst.quota.locking_thread() == old_dst.quota.locking_thread()
    &&& new_dst.quota.being_killed() == old_dst.quota.being_killed()
    &&& new_dst.total_free_pages.view() == old_dst.total_free_pages.view() + 1
}

proof fn kill_container_move_free_page_4k_eof_process_management(
    pre: KernelK, post: KernelK, src: RwLockContainerPtr, dst: RwLockContainerPtr, src_allocator: RwLockPageAllocatorPtr, dst_allocator: RwLockPageAllocatorPtr,
    page_ptr: PagePtr, node: usize,
)
    requires
        pre.inv(),
        src != dst,
        pre.ctn_mp.dom().contains(src),
        pre.ctn_mp.dom().contains(dst),
        kill_container_move_free_page_4k_eof_transition_framing(pre, post, src, dst, src_allocator, dst_allocator, page_ptr, node),
        post.subsystems_inv(),
    ensures
        post.process_management_inv(),
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush),
{
    hide(Seq::contains);
    reveal(kill_container_move_free_page_4k_eof_transition_framing);
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { container_cpu_offline_flags_wf_preserved_for_flags_owner_eq(pre.ctn_mp, post.ctn_mp, pre.cpu_offline_mp, post.cpu_offline_mp); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by {
        container_cpu_wf_preserved_for_container_cpu_fields_eq(pre.ctn_mp, post.ctn_mp, post.cpu_set_mp, post.cpu_arr); reveal(container_thread_wf); reveal(container_process_wf); reveal(process_thread_wf);
    };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf);
        container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp);
    };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(container_process_wf); reveal(process_pcid_allocator_wf); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
        reveal(container_thread_wf); reveal(container_scheduler_wf); container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp);
    };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(container_cpu_wf);
    };
}

proof fn kill_container_move_free_page_4k_eof_free_pages(
    pre: KernelK, post: KernelK, src: RwLockContainerPtr, dst: RwLockContainerPtr, src_allocator: RwLockPageAllocatorPtr, dst_allocator: RwLockPageAllocatorPtr,
    page_ptr: PagePtr, node: usize,
)
    requires
        pre.inv(),
        src != dst,
        src_allocator != dst_allocator,
        page_ptr_valid(page_ptr),
        index_valid(NUM_PAGES, page_ptr2page_index(page_ptr)),
        pre.allc_4k_mp.dom().contains(src_allocator),
        pre.allc_4k_mp.dom().contains(dst_allocator),
        pre.allc_4k_mp.spec_index(src_allocator).owning_container == src,
        pre.allc_4k_mp.spec_index(dst_allocator).owning_container == dst,
        pre.allc_4k_mp.spec_index(src_allocator).global_pool.view().view().len() > 0,
        pre.allc_4k_mp.spec_index(src_allocator).global_pool.view().view().spec_index(0) == page_ptr,
        pre.allc_4k_mp.spec_index(src_allocator).global_pool.view().view().no_duplicates(),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(src_allocator), state: FreePageAllocatorState::GlobalList }),
        !pre.allc_4k_mp.spec_index(dst_allocator).global_pool.view().view().contains(page_ptr),
        node == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list_node_storage.addr(),
        kill_container_move_free_page_4k_eof_transition_framing(pre, post, src, dst, src_allocator, dst_allocator, page_ptr, node),
    ensures
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
{
    reveal(kill_container_move_free_page_4k_eof_transition_framing);
    seq_skip_lemma::<PagePtr>(); pre.allc_4k_mp.spec_index(dst_allocator).global_pool.view().view().insert_ensures(0, page_ptr);
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_cpu_cache_free_4k_page_wf(post.allc_4k_mp, post.pg_arr) && container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf);
    };
    reveal(container_allocator_free_4k_page_wf);
}

/// Closes every invariant after `kill_container_move_free_page_4k`.
pub(super) proof fn kill_container_move_free_page_4k_eof(
    pre: KernelK, post: KernelK, src: RwLockContainerPtr, dst: RwLockContainerPtr, src_allocator: RwLockPageAllocatorPtr, dst_allocator: RwLockPageAllocatorPtr,
    page_ptr: PagePtr, node: usize,
)
    requires
        pre.inv(),
        src != dst,
        src_allocator != dst_allocator,
        page_ptr_valid(page_ptr),
        index_valid(NUM_PAGES, page_ptr2page_index(page_ptr)),
        pre.ctn_mp.dom().contains(src),
        pre.ctn_mp.dom().contains(dst),
        pre.ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_4k == src_allocator,
        pre.ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_4k == dst_allocator,
        pre.ctn_mp.spec_index(src).view_ghost().uppertree_seq.view().contains(dst),
        pre.allc_4k_mp.dom().contains(src_allocator),
        pre.allc_4k_mp.dom().contains(dst_allocator),
        pre.allc_4k_mp.spec_index(src_allocator).owning_container == src,
        pre.allc_4k_mp.spec_index(dst_allocator).owning_container == dst,
        pre.allc_4k_mp.spec_index(src_allocator).global_pool.view().view().len() > 0,
        pre.allc_4k_mp.spec_index(src_allocator).global_pool.view().view().spec_index(0) == page_ptr,
        pre.allc_4k_mp.spec_index(src_allocator).global_pool.view().view().no_duplicates(),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(src_allocator), state: FreePageAllocatorState::GlobalList }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == src,
        !pre.allc_4k_mp.spec_index(dst_allocator).global_pool.view().view().contains(page_ptr),
        node == pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list_node_storage.addr(),
        kill_container_move_free_page_4k_eof_transition_framing(pre, post, src, dst, src_allocator, dst_allocator, page_ptr, node),
        0 < pre.allc_4k_mp.spec_index(src_allocator).quota.view().value,
        pre.allc_4k_mp.spec_index(dst_allocator).quota.view().value < usize::MAX,
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(src_allocator).wf(),
        post.allc_4k_mp.spec_index(dst_allocator).wf(),
    ensures
        post.inv(),
{
    reveal(kill_container_move_free_page_4k_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); reveal(Page::mappings_va_valid); };
    assert(container_tree_fields_wf(post.ctn_mp)) by { reveal(container_tree_fields_wf); reveal(container_perms_wf); };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); };
    kill_container_move_free_page_4k_eof_free_pages(pre, post, src, dst, src_allocator, dst_allocator, page_ptr, node);
    assert(post.memory_management_inv()) by {
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
            allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
            allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
        };
        assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_page_owner_wf); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { page_array_wf_at(pre.pg_arr, page_index); reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
        assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
        assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf);
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
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, src); container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, dst);
            reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf);
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            container_process_allocator_quota_2m_wf_preserved_for_container_allocator_eq(pre.ctn_mp, post.ctn_mp, post.prc_mp, post.thr_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_4k_mp, pre.allc_1g_mp);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by { reveal(container_process_allocator_quota_1g_wf); };
        assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            container_uppertree_seq_wf_at(pre.rt_ctn, pre.ctn_mp, src, dst); reveal(container_kill_retire_wf); reveal(container_allocator_wf);
        };
        assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp);
        };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
    };
    kill_container_move_free_page_4k_eof_process_management(pre, post, src, dst, src_allocator, dst_allocator, page_ptr, node);
}
} // verus!
