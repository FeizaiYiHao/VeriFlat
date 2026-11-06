use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::remove_last_held_1g_mapping_eof::*;

verus! {
/// Drop the record `(pagetable, va)` of a held 1G leaf from the page `pg_ptr`, whose last mapping it was, push the page onto the head of the owner allocator's 1G global pool, credit the thread's pending free 1G quota at the owner's `depth`, and clear the leaf. The leaf's root entry no
/// longer resolves or the leaf is hidden, and the table lists no CPU stale; the caller holds the page, the pool, the thread and the table. No 1G CPU cache is touched.
pub fn remove_last_held_1g_mapping_to_allocator(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize,
    allc_ptr: RwLockPageAllocatorPtr, counter: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, page_perm: Tracked<&LockPerm>, pagetable_perm: Tracked<&LockPerm>,
    thread_perm: Tracked<&LockPerm>, pool_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_1g_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == pg_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None
            || !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.perm.present,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        page_ptr_valid(pg_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped1g,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().contains((pagetable, va)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count == 1,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == owner,
        old(krnl).allc_1g_mp.dom().contains(allc_ptr),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_1g_lock_map(), allc_ptr, TypedLockMode::Write),
        pool_perm.view().state() is WriteLock,
        pool_perm.view().thread_id() == old(lctx).thread_id(),
        pool_perm.view().lock_id() == old(krnl).allc_1g_mp.spec_index(allc_ptr).global_pool.locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_1g == allc_ptr,
        depth <= old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth,
        if depth == old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { owner == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container } else { old(krnl).thrd_mp.spec_index(thrd_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
        *old(counter) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_1g_at_depth(depth),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_lower == old(krnl).pt_lower,
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& new_c.lower == old_c.lower
            &&& new_c.higher == (PageTableHigher { l3_tables: new_c.higher.l3_tables, mapping_1g: new_c.higher.mapping_1g, ..old_c.higher })
            &&& new_c.mapping_1g() == old_c.mapping_1g().remove(va)
            &&& new_c.page_closure() == old_c.page_closure()
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_l3(l4i, l3i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> new_c.spec_held_l3(l4i, l3i) == old_c.spec_held_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_resolve_mapping_l3(l4i, l3i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> new_c.spec_resolve_mapping_l3(l4i, l3i) == old_c.spec_resolve_mapping_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_1g_l3(l4i, l3i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (spec_v2l4index(va), spec_v2l3index(va)) ==> new_c.spec_held_1g_l3(l4i, l3i) == old_c.spec_held_1g_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_resolve_mapping_1g_l3(l4i, l3i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (spec_v2l4index(va), spec_v2l3index(va))
                    ==> new_c.spec_resolve_mapping_1g_l3(l4i, l3i) == old_c.spec_resolve_mapping_1g_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
            &&& new_c.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
            &&& new_c.spec_resolve_mapping_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
        }),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().remove((pagetable, va)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Free1g { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::GlobalList }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread(),
        *final(counter) == *old(counter) + 1,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_1g_at_depth(depth) == *final(counter),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        held_threads_unchanged_except(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx), set![thrd_ptr]),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g,
            indirect_free_quota_pending_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g.view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g.view() + if depth == old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { 1int } else { 0int },
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view()
            == if depth < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view().update(depth as int, *final(counter)) }
            else { old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view() },
        final(krnl).allc_1g_mp.unchanged_except(&old(krnl).allc_1g_mp, allc_ptr),
        final(krnl).allc_1g_mp.spec_index(allc_ptr).global_pool.locking_thread() == old(krnl).allc_1g_mp.spec_index(allc_ptr).global_pool.locking_thread(),
        final(krnl).allc_1g_mp.spec_index(allc_ptr).global_pool.view().view() == old(krnl).allc_1g_mp.spec_index(allc_ptr).global_pool.view().view().insert(0, pg_ptr),
        final(krnl).allc_1g_mp.spec_index(allc_ptr).total_free_pages.view() == old(krnl).allc_1g_mp.spec_index(allc_ptr).total_free_pages.view() + 1,
        final(krnl).allc_1g_mp.spec_index(allc_ptr).quota == old(krnl).allc_1g_mp.spec_index(allc_ptr).quota,
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    assert(krnl.allc_1g_mp.spec_index(allc_ptr).total_free_pages.view() < usize::MAX) by { kernel_inv_implies_container_allocator_1g_quota_bounded(krnl, owner); };
    assert(krnl.allc_1g_mp.spec_index(allc_ptr).quota.view().value as int + *counter as int <= krnl.allc_1g_mp.spec_index(allc_ptr).total_free_pages.view()) by { kernel_inv_implies_thread_pending_1g_quota_bounded(krnl, thrd_ptr, owner, depth); };
    let pg_idx = page_ptr2page_index(pg_ptr);
    let l4i = v2l4index(va);
    let l3i = v2l3index(va);
    proof { spec_va_1g_valid_index_roundtrip(va); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
    assert(krnl.pg_arr.spec_index(pg_idx).view().view().addr == pg_ptr && index_valid(NUM_PAGES, pg_idx) && krnl.pg_arr.spec_index(pg_idx).view().is_init()
        && krnl.pg_arr.spec_index(pg_idx).view().view().inv() && krnl.pg_arr.inv()) by {
        page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx); page_ptr_roundtrip();
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    assert(krnl.thrd_mp.spec_index(thrd_ptr).is_init() && krnl.allc_1g_mp.perms_wf() && krnl.allc_1g_mp.spec_index(allc_ptr).wf()
        && !krnl.allc_1g_mp.spec_index(allc_ptr).global_pool.view().view().contains(pg_ptr)) by {
        thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); allocator_perms_wf_map(krnl.allc_1g_mp); allocator_perms_wf_at(krnl.allc_1g_mp, allc_ptr);
        allocator_free_1g_pages_wf_global_at(krnl.allc_1g_mp, krnl.pg_arr, allc_ptr, pg_ptr);
    };
    let (node_addr, node_perm) = {
        let page = krnl.pg_arr.borrow_mut_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), page_perm);
        remove_last_1g_mapping_to_global_pool(page, pagetable, va, allc_ptr)
    };
    krnl.allc_1g_mp.push_global_pool_page_typed(allc_ptr, node_addr, node_perm, Ghost(lctx.allocator_quota_1g_lock_map()), Ghost(lctx.allocator_cache_1g_lock_map()),
        Ghost(lctx.allocator_global_pool_1g_lock_map()), Tracked(&*lctx), pool_perm);
    thread_map_add_free_quota_pending_1g(&mut krnl.thrd_mp, thrd_ptr, depth, counter, Tracked(&*lctx), thread_perm);
    pagetable_map_clear_held_1g_leaf(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, (l4i, l3i), Tracked(&mut *lctx), pagetable_perm);
    proof {
        lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
        assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(pg_idx), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write })) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
        };
        assert(remove_last_held_1g_mapping_to_allocator_eof_transition_framing(*old(krnl), *krnl, pagetable, va, pg_ptr, thrd_ptr, depth, allc_ptr, *old(counter), *counter, node_addr)) by {
            reveal(remove_last_held_1g_mapping_to_allocator_eof_transition_framing);
        };
        remove_last_held_1g_mapping_to_allocator_eof(*old(krnl), *krnl, pagetable, va, pg_ptr, thrd_ptr, owner, depth, allc_ptr, *old(counter), *counter, node_addr);
        held_threads_unchanged_except_for_unchanged_except(old(krnl).thrd_mp, krnl.thrd_mp, old(lctx), thrd_ptr);
    }
}

/// Drop the last mapping `(pagetable_ptr, va)` of the mapped 1G page and turn it into a free page on the global list of the 1G allocator `allc_ptr`, returning its free-list node.
pub fn remove_last_1g_mapping_to_global_pool(page: &mut Page, pagetable_ptr: RwLockPageTableRoot, va: VAddr, allc_ptr: RwLockPageAllocatorPtr) -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
    requires
        old(page).inv(),
        old(page).state is Mapped1g,
        old(page).mappings().contains((pagetable_ptr, va)),
        old(page).ref_count == 1,
    ensures
        final(page).inv(),
        final(page).state == (PageState::Free1g { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::GlobalList }),
        final(page).mappings() == Set::<(RwLockPageTableRoot, VAddr)>::empty(),
        final(page).mappings() == old(page).mappings().remove((pagetable_ptr, va)),
        ret.0 == old(page).free_list_node_storage.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == old(page).addr,
        final(page).free_list_node_storage.addr() == old(page).free_list_node_storage.addr(),
        *final(page) == (Page { state: final(page).state, mappings: final(page).mappings, ref_count: 0, free_list_node_storage: final(page).free_list_node_storage, ..*old(page) }),
{
    proof { reveal(Page::mappings_va_valid); }
    let (node_addr, mut node_perm) = page.free_list_node_storage.take();
    node_update_value(node_addr, &mut node_perm, page.addr);
    page.mappings = Ghost(Set::empty());
    page.ref_count = 0;
    page.state = PageState::Free1g { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::GlobalList };
    (node_addr, node_perm)
}
}
