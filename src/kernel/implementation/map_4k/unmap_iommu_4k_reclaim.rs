use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::unmap_iommu_4k_reclaim_eof::reclaim_last_iommu_4k_mapping_to_cpu_cache_eof;
#[cfg(verus_keep_ghost)]
use super::unmap_iommu_4k_reclaim_spec::reclaim_last_iommu_4k_mapping_to_cpu_cache_transition;

verus! {
/// Unmaps one hidden 4K leaf of a write-locked IOMMU table whose page has no other mapping, returns the page to the
/// allocator CPU cache, and increments the owning thread's pending free-quota counter.
pub fn remove_last_iommu_4k_mapping_to_allocator(
    krnl: &mut KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, allocator_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, counter: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, iommu_table_perm: Tracked<&LockPerm>, page_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
    cache_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).it_mp.dom().contains(iommu_table),
        pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va(indices)),
        !old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).present,
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).addr == page_ptr,
        page_ptr_valid(page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == 1,
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        cache_perm.view().state() is WriteLock,
        cache_perm.view().thread_id() == old(lctx).thread_id(),
        cache_perm.view().lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        depth <= old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth,
        if depth == old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth { owner == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container } else { old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
        *old(counter) == old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        iommu_table_perm.view().state() is WriteLock,
        iommu_table_perm.view().thread_id() == old(lctx).thread_id(),
        iommu_table_perm.view().lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { it_mp: final(krnl).it_mp, pg_arr: final(krnl).pg_arr, thr_mp: final(krnl).thr_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table).being_killed() == old(krnl).it_mp.spec_index(iommu_table).being_killed(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().remove(spec_index2va(indices)),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g(),
        final(krnl).it_mp.spec_index(iommu_table).view().page_closure() == old(krnl).it_mp.spec_index(iommu_table).view().page_closure(),
        final(krnl).it_mp.spec_index(iommu_table).view().kernel_entries == old(krnl).it_mp.spec_index(iommu_table).view().kernel_entries,
        final(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end == old(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end,
        final(krnl).it_mp.spec_index(iommu_table).view().cr3 == old(krnl).it_mp.spec_index(iommu_table).view().cr3,
        final(krnl).it_mp.spec_index(iommu_table).view().proc_ptr == old(krnl).it_mp.spec_index(iommu_table).view().proc_ptr,
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count - 1,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().iommu_mappings()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().iommu_mappings().remove((iommu_table, spec_index2va(indices))),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        *final(counter) == *old(counter) + 1,
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth) == *final(counter),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() + if depth == old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth { 1int } else { 0int },
        final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()
            == if depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth { old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, *final(counter)) }
            else { old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() },
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota,
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() + 1,
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert(0, page_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool == old(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool,
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
{
    assert(krnl.allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() < usize::MAX) by {
        allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        reveal(allocator_free_page_ptrs_wf);
        let allocator = krnl.allc_4k_mp.spec_index(allocator_ptr);
        assert(allocator.global_pool.view().len() <= NUM_PAGES * 4096) by {
            reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list); allocator.global_pool.view().lemma_len_view();
            seq_unique_bounded_usize_len(allocator.global_pool.view().view(), (NUM_PAGES * 4096) as usize);
        };
        assert(allocator.cpu_caches.view().fold_left(0int, |sum: int, cache: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| sum + cache.view().linked_list.len()) <= NUM_CPUS * ALLOCATOR_MAX_WATERMARK) by {
            lemma_cache_len_fold_upper_bound(allocator.cpu_caches);
        };
    };
    assert(krnl.allc_4k_mp.spec_index(allocator_ptr).quota.view().value as int + *counter as int <= krnl.allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view()) by {
        reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); reveal(process_perms_wf); reveal(thread_perms_wf);
        let direct = krnl.ctn_mp.spec_index(owner).view_ghost().owned_threads.view();
        let indirect = krnl.ctn_mp.spec_index(owner).view_ghost().owned_indirect_threads.view();
        lemma_process_effective_quota_4k_fold_nonneg(krnl.ctn_mp.spec_index(owner).view_ghost().owned_processes.view(), krnl.prc_mp);
        let effective = |t: RwLockThreadPtr| thread_effective_quota_4k(krnl.thr_mp.spec_index(t));
        assert((|sum: int, t: RwLockThreadPtr| sum + effective(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_4k(krnl.thr_mp.spec_index(t)))
            && direct.fold(0int, |sum: int, t: RwLockThreadPtr| sum + effective(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(direct, effective); };
        lemma_thread_direct_pending_4k_fold_nonneg(direct, krnl.thr_mp);
        lemma_thread_indirect_pending_4k_fold_nonneg(indirect, krnl.thr_mp, depth as int);
        if depth == krnl.thr_mp.spec_index(thread_ptr).view().container_depth {
            let value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
            assert((|sum: int, t: RwLockThreadPtr| sum + value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view())
                && direct.fold(0int, |sum: int, t: RwLockThreadPtr| sum + value(t)) >= value(thread_ptr)) by { lemma_set_fold_int_sum_ge_member(direct, value, thread_ptr); };
        } else {
            let value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth as int) as int;
            assert((|sum: int, t: RwLockThreadPtr| sum + value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth as int))
                && indirect.fold(0int, |sum: int, t: RwLockThreadPtr| sum + value(t)) >= value(thread_ptr)) by { lemma_set_fold_int_sum_ge_member(indirect, value, thread_ptr); };
        }
    };
    let page_index = page_ptr2page_index(page_ptr);
    let iova = index2va(indices);
    proof {
        iommu_table_perms_wf_at(krnl.it_mp, iommu_table);
        assert(krnl.it_mp.spec_index(iommu_table).view().kernel_l4_end == 0) by { reveal(PageTable::kernel_entries_wf); };
    }
    let l1_ptr;
    {
        let it = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), iommu_table_perm);
        assert(it.spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some) by { reveal(PageTable::wf_mapping_4k); };
        let l4 = it.get_entry_l4(indices.0).unwrap();
        let l3 = it.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        let l2 = it.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
        l1_ptr = l2.addr;
    }
    assert(krnl.pg_arr.spec_index(page_index).view().view().addr == page_ptr && index_valid(NUM_PAGES, page_index) && krnl.pg_arr.spec_index(page_index).view().is_init()
        && krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k && krnl.pg_arr.spec_index(page_index).view().view().iommu_mappings().contains((iommu_table, iova))) by {
        page_ptr_valid_imply_page_index_valid(); page_array_wf_at(krnl.pg_arr, page_index); reveal(page_iommu_table_wf); page_ptr_roundtrip();
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    assert(krnl.thr_mp.spec_index(thread_ptr).is_init() && krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.spec_index(allocator_ptr).wf() && !krnl.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)) by {
        thread_perms_wf_at(krnl.thr_mp, thread_ptr); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf);
    };
    let (node_addr, node_perm) = page_array_remove_last_4k_iommu_mapping_to_cache(&mut krnl.pg_arr, page_index, iommu_table, iova, allocator_ptr, cpu_id, Tracked(&*lctx), page_perm);
    krnl.allc_4k_mp.push_cache_page_typed(allocator_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), cache_perm);
    thread_map_add_free_quota_pending_4k(&mut krnl.thr_mp, thread_ptr, depth, counter, Tracked(&*lctx), thread_perm);
    iommu_table_map_unmap_4k_kernel(&mut krnl.it_mp, iommu_table, indices, l1_ptr, Tracked(&mut *lctx), iommu_table_perm);
    proof {
        lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
        assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(page_index), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write })) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
    }

    proof {
        old(krnl).it_mp.typed_lock_map_aligned_write_at(old(lctx).iommu_table_lock_map(), old(lctx).thread_id(), iommu_table);
        assert(reclaim_last_iommu_4k_mapping_to_cpu_cache_transition(*old(krnl), *krnl, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, *old(counter), *counter, node_addr)) by {
            reveal(reclaim_last_iommu_4k_mapping_to_cpu_cache_transition);
        };
        reclaim_last_iommu_4k_mapping_to_cpu_cache_eof(*old(krnl), *krnl, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, *old(counter), *counter, node_addr);
        held_threads_unchanged_except_for_unchanged_except(old(krnl).thr_mp, krnl.thr_mp, old(lctx), thread_ptr);
    }
}
}
