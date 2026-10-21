use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::unmap_4k_reclaim_eof::reclaim_last_4k_mapping_to_cpu_cache_eof;
#[cfg(verus_keep_ghost)]
use super::unmap_4k_reclaim_spec::reclaim_last_4k_mapping_to_cpu_cache_eof_transition_framing;

verus! {
/// Remove the hidden 4K leaf `va` of `pagetable`, held in write mode iff `write_held`, and move its page, whose last
/// mapping it was, into the owner allocator's CPU cache; the caller holds the leaf's window and page, and no CPU is listed
/// stale for the window.
pub fn remove_last_4k_mapping_to_allocator(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, allocator_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, counter: &mut usize, write_held: bool, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>, page_perm: Tracked<&LockPerm>,
    thread_perm: Tracked<&LockPerm>, cache_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).addr == page_ptr,
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
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, if write_held { TypedLockMode::Write } else { TypedLockMode::Read }),
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        write_held ==> pagetable_perm.view().state() is WriteLock,
        write_held ==> pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        !write_held ==> pagetable_perm.view().state() is ReadLock,
        !write_held ==> old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, WindowVa { va: spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0usize)) }), TypedLockMode::Write),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, thr_mp: final(krnl).thr_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().remove(va),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).page_closure() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).page_closure(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_entries == old(krnl).pt_mp.spec_index(pagetable).view().kernel_entries,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_lock == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_lock,
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count - 1,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings().remove((pagetable, va)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
        !write_held ==> final(krnl).pt_mp == old(krnl).pt_mp,
        *final(counter) == *old(counter) + 1,
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth) == *final(counter),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
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
{
    assert(krnl.allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() < usize::MAX) by { lemma_container_allocator_4k_quota_bounded(krnl, owner); };
    assert(krnl.allc_4k_mp.spec_index(allocator_ptr).quota.view().value as int + *counter as int <= krnl.allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view()) by { lemma_thread_pending_4k_quota_bounded(krnl, thread_ptr, owner, depth); };
    let page_index = page_ptr2page_index(page_ptr);
    let indices = va2index(va);
    assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable).inv() && spec_index2va(indices) == va) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3); };
    proof {
        let window_va = WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) };
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_va);
        assert(spec_v2l4index(window_va.va) == indices.0 && spec_v2l3index(window_va.va) == indices.1 && spec_v2l2index(window_va.va) == indices.2) by {
            broadcast use spec_va_2m_valid_index_roundtrip; spec_index2va_injective();
        };
    }
    let l1_ptr;
    {
        let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm);
        let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable);
        let l4 = pt.get_entry_l4(indices.0).unwrap();
        let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        let l2 = pt.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).unwrap();
        l1_ptr = l2.addr;
    }
    assert(krnl.pg_arr.spec_index(page_index).view().view().addr == page_ptr && index_valid(NUM_PAGES, page_index) && krnl.pg_arr.spec_index(page_index).view().is_init()
        && krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k && krnl.pg_arr.spec_index(page_index).view().view().mappings().contains((pagetable, va))) by {
        page_ptr_valid_imply_page_index_valid(); page_array_wf_at(krnl.pg_arr, page_index); mapped_4k_page_pagetable_wf_pagetable_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, va); page_ptr_roundtrip();
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    assert(krnl.thr_mp.spec_index(thread_ptr).is_init() && krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.spec_index(allocator_ptr).wf() && !krnl.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)) by {
        thread_perms_wf_at(krnl.thr_mp, thread_ptr); allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        container_allocator_free_4k_page_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allocator_ptr, cpu_id, page_ptr);
    };
    let (node_addr, node_perm) = page_array_remove_last_4k_mapping_to_cache(&mut krnl.pg_arr, page_index, pagetable, va, allocator_ptr, cpu_id, Tracked(&*lctx), page_perm);
    krnl.allc_4k_mp.push_cache_page_typed(allocator_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), cache_perm);
    thread_map_add_free_quota_pending_4k(&mut krnl.thr_mp, thread_ptr, depth, counter, Tracked(&*lctx), thread_perm);
    if write_held {
        pagetable_map_unmap_4k_kernel(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, indices, l1_ptr, Tracked(&mut *lctx), pagetable_perm);
    } else {
        pagetable_map_unmap_4k_kernel_rlocked(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, indices, l1_ptr, Tracked(&mut *lctx), pagetable_perm);
    }
    proof {
        lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
        assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(page_index), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write })) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
    }

    proof {
        assert(reclaim_last_4k_mapping_to_cpu_cache_eof_transition_framing(*old(krnl), *krnl, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, *old(counter), *counter, node_addr)) by {
            reveal(reclaim_last_4k_mapping_to_cpu_cache_eof_transition_framing);
        };
        reclaim_last_4k_mapping_to_cpu_cache_eof(*old(krnl), *krnl, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, *old(counter), *counter, node_addr);
        held_threads_unchanged_except_for_unchanged_except(old(krnl).thr_mp, krnl.thr_mp, old(lctx), thread_ptr);
    }
}
}
