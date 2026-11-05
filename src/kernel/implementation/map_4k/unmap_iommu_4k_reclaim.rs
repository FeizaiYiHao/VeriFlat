use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::unmap_iommu_4k_reclaim_eof::reclaim_last_iommu_4k_mapping_to_cpu_cache_eof;
#[cfg(verus_keep_ghost)]
use super::unmap_iommu_4k_reclaim_spec::reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing;

verus! {
/// Unmaps one 4K leaf of a write-locked IOMMU table whose page has no other mapping, returns the page to the allocator CPU
/// cache, and increments the owning thread's pending free-quota counter. The leaf is hidden iff `!was_present`; a present
/// leaf requires a table without a domain id, and its removal also drops the leaf from the table's user view.
pub fn remove_last_iommu_4k_mapping_to_allocator(
    krnl: &mut KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), pg_ptr: PagePtr, l1_ptr: PageMapPtr, thrd_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize,
    allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, counter: &mut usize, Ghost(was_present): Ghost<bool>, Tracked(lctx): Tracked<&mut LocalContext>, iommu_table_perm: Tracked<&LockPerm>,
    page_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>, cache_perm: Tracked<&LockPerm>,
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
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).present == was_present,
        was_present ==> old(krnl).it_mp.spec_index(iommu_table).view().did is None,
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).addr == pg_ptr,
        old(krnl).it_mp.spec_index(iommu_table).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        old(krnl).it_mp.spec_index(iommu_table).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == l1_ptr,
        page_ptr_valid(pg_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count == 1,
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().is_io_page,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == owner,
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).allc_4k_mp.dom().contains(allc_ptr),
        old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allc_ptr, cpu_id), TypedLockMode::Write),
        cache_perm.view().state() is WriteLock,
        cache_perm.view().thread_id() == old(lctx).thread_id(),
        cache_perm.view().lock_id() == old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allc_ptr,
        depth <= old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth,
        if depth == old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { owner == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container } else { old(krnl).thrd_mp.spec_index(thrd_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
        *old(counter) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_4k_at_depth(depth),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        iommu_table_perm.view().state() is WriteLock,
        iommu_table_perm.view().thread_id() == old(lctx).thread_id(),
        iommu_table_perm.view().lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
        !was_present ==> iommu_table_tlb_entries_present(old(krnl).iommu_tlb, old(krnl).irt.view(), old(krnl).it_mp, iommu_table),
    ensures
        final(krnl).inv(),
        iommu_table_tlb_entries_present(final(krnl).iommu_tlb, final(krnl).irt.view(), final(krnl).it_mp, iommu_table),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { it_mp: final(krnl).it_mp, pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
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
        final(krnl).it_mp.spec_index(iommu_table).view().did == old(krnl).it_mp.spec_index(iommu_table).view().did,
        was_present ==> final(krnl).it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k
            == old(krnl).it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k.remove(spec_index2va(indices)),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count - 1,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().iommu_mappings()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().iommu_mappings().remove((iommu_table, spec_index2va(indices))),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().being_killed() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().being_killed(),
        *final(counter) == *old(counter) + 1,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_4k_at_depth(depth) == *final(counter),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        held_threads_unchanged_except(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx), set![thrd_ptr]),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view() + if depth == old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { 1int } else { 0int },
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view()
            == if depth < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, *final(counter)) }
            else { old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view() },
        final(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allc_ptr),
        final(krnl).allc_4k_mp.spec_index(allc_ptr).quota == old(krnl).allc_4k_mp.spec_index(allc_ptr).quota,
        final(krnl).allc_4k_mp.spec_index(allc_ptr).total_free_pages.view() == old(krnl).allc_4k_mp.spec_index(allc_ptr).total_free_pages.view() + 1,
        final(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view() == old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert(0, pg_ptr),
        final(krnl).allc_4k_mp.spec_index(allc_ptr).global_pool == old(krnl).allc_4k_mp.spec_index(allc_ptr).global_pool,
        !was_present ==> kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        was_present ==> kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &KernelK { it_mp: old(krnl).it_mp, ..*final(krnl) }),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    assert(krnl.allc_4k_mp.spec_index(allc_ptr).total_free_pages.view() < usize::MAX) by { lemma_container_allocator_4k_quota_bounded(krnl, owner); };
    assert(krnl.allc_4k_mp.spec_index(allc_ptr).quota.view().value as int + *counter as int <= krnl.allc_4k_mp.spec_index(allc_ptr).total_free_pages.view()) by { lemma_thread_pending_4k_quota_bounded(krnl, thrd_ptr, owner, depth); };
    let pg_idx = page_ptr2page_index(pg_ptr);
    let iova = index2va(indices);
    proof { iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table); }
    assert(krnl.pg_arr.spec_index(pg_idx).view().view().addr == pg_ptr && index_valid(NUM_PAGES, pg_idx) && krnl.pg_arr.spec_index(pg_idx).view().is_init()
        && krnl.pg_arr.spec_index(pg_idx).view().view().state is Mapped4k && krnl.pg_arr.spec_index(pg_idx).view().view().iommu_mappings().contains((iommu_table, iova))) by {
        page_ptr_valid_imply_page_index_valid(); page_array_wf_at(krnl.pg_arr, pg_idx); page_iommu_table_wf_table_at(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr, iommu_table, iova); page_ptr_roundtrip();
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    assert(krnl.thrd_mp.spec_index(thrd_ptr).is_init() && krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.spec_index(allc_ptr).wf() && !krnl.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)) by {
        thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allc_ptr);
        allocator_free_4k_pages_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allc_ptr, cpu_id, pg_ptr);
    };
    let (node_addr, node_perm) = page_array_remove_last_4k_iommu_mapping_to_cache(&mut krnl.pg_arr, pg_idx, iommu_table, iova, allc_ptr, cpu_id, Tracked(&*lctx), page_perm);
    krnl.allc_4k_mp.push_cache_page_typed(allc_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), cache_perm);
    thread_map_add_free_quota_pending_4k(&mut krnl.thrd_mp, thrd_ptr, depth, counter, Tracked(&*lctx), thread_perm);
    iommu_table_map_unmap_4k_kernel(&mut krnl.it_mp, iommu_table, indices, l1_ptr, Tracked(&mut *lctx), iommu_table_perm);
    proof {
        lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
        assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(pg_idx), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write })) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
        };
    }

    proof {
        old(krnl).it_mp.typed_lock_map_aligned_write_at(old(lctx).iommu_table_lock_map(), old(lctx).thread_id(), iommu_table);
        assert(reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing(*old(krnl), *krnl, iommu_table, indices, pg_ptr, thrd_ptr, depth, allc_ptr, cpu_id, *old(counter), *counter, node_addr)) by {
            reveal(reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing);
        };
        reclaim_last_iommu_4k_mapping_to_cpu_cache_eof(*old(krnl), *krnl, iommu_table, indices, pg_ptr, thrd_ptr, owner, depth, allc_ptr, cpu_id, *old(counter), *counter, node_addr, was_present);
        held_threads_unchanged_except_for_unchanged_except(old(krnl).thrd_mp, krnl.thrd_mp, old(lctx), thrd_ptr);
    }
}
}
