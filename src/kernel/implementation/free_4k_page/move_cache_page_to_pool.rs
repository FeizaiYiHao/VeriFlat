use vstd::prelude::*;
use crate::*;

verus! {
pub fn move_cache_page_to_pool(krnl: &mut KernelK, allocator: RwLockPageAllocatorPtr, cpu_id: CpuId, page_ptr: PagePtr, Tracked(lctx): Tracked<&mut LocalContext>, cache_perm: Tracked<&LockPerm>, pool_perm: Tracked<&LockPerm>, page_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).allc_4k_mp.dom().contains(allocator),
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(page_ptr),
        old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
        old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().spec_index(0) == page_ptr,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator, cpu_id), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_4k_lock_map(), allocator, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        cache_perm.view().state() is WriteLock,
        cache_perm.view().thread_id() == old(lctx).thread_id(),
        cache_perm.view().lock_id() == old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        pool_perm.view().state() is WriteLock,
        pool_perm.view().thread_id() == old(lctx).thread_id(),
        pool_perm.view().lock_id() == old(krnl).allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).lock_id_set() == old(lctx).lock_id_set(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::GlobalList }, ..old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view() }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator),
        final(krnl).allc_4k_mp.spec_index(allocator).total_free_pages == old(krnl).allc_4k_mp.spec_index(allocator).total_free_pages,
        final(krnl).allc_4k_mp.spec_index(allocator).quota == old(krnl).allc_4k_mp.spec_index(allocator).quota,
        final(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view() == old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().skip(1),
        final(krnl).allc_4k_mp.spec_index(allocator).global_pool.view().view() == old(krnl).allc_4k_mp.spec_index(allocator).global_pool.view().view().insert(0, page_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        final(krnl).allc_4k_mp.spec_index(allocator).global_pool.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator).global_pool.locking_thread(),
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
{
    let page_index = page_ptr2page_index(page_ptr);
    assert(krnl.pg_arr.inv() && krnl.pg_arr.spec_index(page_index).view().inv() && krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.spec_index(allocator).wf()) by { reveal(page_array_wf); reveal(allocator_perms_wf); page_ptr_valid_imply_page_index_valid(); };
    assert(krnl.pg_arr.spec_index(page_index).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::PreCpuCache { cpu_id } }) && !krnl.allc_4k_mp.spec_index(allocator).global_pool.view().view().contains(page_ptr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); };
    let (node_addr, Tracked(node_perm)) = krnl.allc_4k_mp.pop_cache_page_typed(allocator, cpu_id, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), cache_perm);
    assert(node_addr == krnl.pg_arr.spec_index(page_index).view().view().free_list_node_storage.addr()) by {
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf);
        old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().linked_list.lemma_value_addr_unique(node_addr, krnl.pg_arr.spec_index(page_index).view().view().free_list_node_storage.addr());
    };
    krnl.allc_4k_mp.push_global_pool_page_typed(allocator, node_addr, Tracked(node_perm), Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), pool_perm);
    let page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), page_perm);
    page.state = PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::GlobalList };
    proof {
        lctx.enter_kernel_view_release();
        assert(krnl.subsystems_inv()) by { reveal(allocator_perms_wf); reveal(page_array_wf); reveal(KernelK::default_pagetable_wf); };
        assert(krnl.memory_management_inv()) by {
            assert(cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr)) by { reveal(cpu_set_pages_wf); };
            assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                allocator_4k_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_4k_mp, krnl.allc_4k_mp);
                allocator_2m_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_2m_mp, krnl.allc_2m_mp);
                allocator_1g_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_1g_mp, krnl.allc_1g_mp);
            };
            assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).pg_arr, krnl.pg_arr); };
            assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
            assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).ctn_mp, krnl.ctn_mp); };
            assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).prc_mp, krnl.prc_mp); };
            assert(container_allocator_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_allocator_wf); };
            assert(allocator_free_page_ptrs_wf(krnl.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
            assert(hugepage_2m_wf(krnl.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
            assert(hugepage_1g_wf(krnl.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
            assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
            assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
            assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
            assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).pcid_allc_mp, krnl.pcid_allc_mp); };
            assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
            assert(scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr)) by { reveal(scheduler_pages_wf); };
            assert(thread_staged_pages_4k_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
            assert(thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr)) by {
                thread_staged_pages_2m_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                thread_staged_pages_1g_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
            };
            assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(krnl).ep_mp, krnl.ep_mp, old(krnl).pg_arr, krnl.pg_arr); };
            assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { lemma_no_change_imply_process_pagetable_match_forall(); };
            assert(process_iommu_table_match(krnl.prc_mp, krnl.it_mp)) by { lemma_no_change_imply_process_iommu_table_match_forall(); };
            assert(krnl.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
            assert(container_process_allocator_quota_4k_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
            assert(container_allocator_cpu_cache_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr) && container_allocator_global_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by {
                reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list); reveal(page_array_wf);
                page_ptr_valid_imply_page_index_valid(); seq_skip_lemma::<PagePtr>();
                broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements;
                broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
                old(krnl).allc_4k_mp.spec_index(allocator).global_pool.view().view().insert_ensures(0, page_ptr);
            };
            assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); };
            assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(krnl.allc_2m_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
            assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(krnl.allc_1g_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
        };
        assert(typed_lock_maps_aligned(krnl, lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
    }
}
}
