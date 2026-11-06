use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::reclaim_held_1g_page_eof::*;
use super::remove_last_held_1g_mapping::remove_last_held_1g_mapping_to_allocator;

verus! {
/// Reclaim the held 1G leaf `va` of the write-held `pagetable`, whose L4 entry no longer resolves or which is hidden, and which lists no CPU stale: lock the page `pg_ptr` the leaf names, drop the record `(pagetable, va)` or push the page behind the last mapping onto the owner's 1G global
/// pool and clear the leaf in the same step, and unlock the page. No 1G CPU cache is touched, so no step boundary is recorded; every other held entry of the table stays.
pub fn reclaim_held_1g_page(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize,
    Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_GLOBAL_POOL_1G_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable || old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view_rodata().view().owning_container == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
        *old(direct) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g.view(),
        forall|depth: int| #![trigger old(indirect)[depth]] 0 <= depth < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> old(indirect)[depth] == old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        va_1g_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == pg_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None
            || !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.perm.present,
        page_ptr_valid(pg_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped1g,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().contains((pagetable, va)),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        held_threads_unchanged_except(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx), set![thrd_ptr]),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g,
            indirect_free_quota_pending_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        *final(direct) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g.view(),
        forall|depth: int| #![trigger final(indirect)[depth]] 0 <= depth < final(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth ==> final(indirect)[depth] == final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view().spec_index(depth),
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
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_1g_l3(l4i, l3i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (spec_v2l4index(va), spec_v2l3index(va)) ==> new_c.spec_held_1g_l3(l4i, l3i) == old_c.spec_held_1g_l3(l4i, l3i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
            &&& new_c.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
        }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().remove((pagetable, va)),
{
    let pg_idx = page_ptr2page_index(pg_ptr);
    proof { page_ptr_valid_imply_page_index_valid(); }
    let Tracked(page_perm) = krnl.wlock_page(pg_idx, Tracked(&mut *lctx));
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx); }
    let page = krnl.pg_arr.borrow_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm));
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    if page.ref_count > 1 {
        remove_held_1g_mapping_without_free(krnl, pagetable, va, pg_ptr, Tracked(&mut *lctx), pagetable_perm, Tracked(&page_perm));
        proof {
            assert(held_threads_unchanged_except(old(krnl).thrd_mp, krnl.thrd_mp, old(lctx), set![thrd_ptr])) by { old(krnl).thrd_mp.typed_lock_map_aligned_held_in_dom(old(lctx).thread_lock_map(), old(lctx).thread_id()); };
        }
    } else {
        let owner = page.owning_container;
        proof { assert(krnl.ctn_mp.dom().contains(owner)) by { container_owned_pages_wf_backward_at(krnl.ctn_mp, krnl.pg_arr, pg_idx); }; container_perms_wf_at(krnl.ctn_mp, owner); }
        let owner_ro = krnl.ctn_mp.borrow_rodata(owner).borrow();
        let depth = owner_ro.depth;
        let allc_ptr = owner_ro.allocator_ptr_1g;
        proof { thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); }
        let thread = krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_perm);
        let thread_depth = thread.container_depth;
        proof {
            let thread_owner = thread.owning_container;
            container_process_page_pagetable_wf_at(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr, pg_idx, pagetable, va);
            process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, thread.owning_proc);
            container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); container_thread_wf_uppertree_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); container_perms_wf_at(krnl.ctn_mp, thread_owner);
            container_subtree_set_wf_at(krnl.rt_ctn, krnl.ctn_mp, owner, thread_owner);
            assert(krnl.allc_1g_mp.dom().contains(allc_ptr)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); };
        }
        let Tracked(pool_perm) = krnl.wlock_allocator_global_pool_1g_ordered(allc_ptr, Tracked(&mut *lctx));
        let mut counter = if depth == thread_depth { *direct } else { indirect[depth] };
        remove_last_held_1g_mapping_to_allocator(krnl, pagetable, va, pg_ptr, thrd_ptr, owner, depth, allc_ptr, &mut counter, Tracked(&mut *lctx), Tracked(&page_perm), pagetable_perm, thread_perm,
            Tracked(&pool_perm));
        if depth == thread_depth { *direct = counter; } else { indirect[depth] = counter; }
        krnl.wunlock_allocator_global_pool_1g(allc_ptr, Tracked(&mut *lctx), Tracked(pool_perm));
        proof {
            assert(lctx.allocator_global_pool_1g_lock_map() =~= old(lctx).allocator_global_pool_1g_lock_map());
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
    }
    krnl.wunlock_page(pg_idx, Tracked(&mut *lctx), Tracked(page_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
        };
        assert(held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx))) by { old(krnl).ctn_mp.typed_lock_map_aligned_held_in_dom(old(lctx).container_lock_map(), old(lctx).thread_id()); };
        assert(held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx))) by { old(krnl).prc_mp.typed_lock_map_aligned_held_in_dom(old(lctx).process_lock_map(), old(lctx).thread_id()); };
        assert(held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx))) by { old(krnl).it_mp.typed_lock_map_aligned_held_in_dom(old(lctx).iommu_table_lock_map(), old(lctx).thread_id()); };
        assert(held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx))) by { reveal(LockedArray::typed_lock_map_aligned); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
}

/// Drop the record `(pagetable, va)` of a held 1G leaf from the page `pg_ptr`, which keeps other references, and clear that leaf; its root entry no longer resolves or the leaf is hidden, and the table lists no CPU stale. The caller holds the page and the table.
pub fn remove_held_1g_mapping_without_free(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>,
    page_perm: Tracked<&LockPerm>)
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
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count > 1,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped1g,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().contains((pagetable, va)),
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
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
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
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    let pg_idx = page_ptr2page_index(pg_ptr);
    let l4i = v2l4index(va);
    let l3i = v2l3index(va);
    proof { spec_va_1g_valid_index_roundtrip(va); page_ptr_valid_imply_page_index_valid(); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
    assert(krnl.pg_arr.inv() && krnl.pg_arr.spec_index(pg_idx).view().is_init() && krnl.pg_arr.spec_index(pg_idx).view().view().inv()) by { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx); };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    {
        let page = krnl.pg_arr.borrow_mut_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), page_perm);
        remove_shared_1g_mapping(page, pagetable, va);
    }
    pagetable_map_clear_held_1g_leaf(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, (l4i, l3i), Tracked(&mut *lctx), pagetable_perm);
    proof {
        lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
        assert(remove_held_1g_mapping_without_free_eof_transition_framing(*old(krnl), *krnl, pagetable, va, pg_ptr)) by { reveal(remove_held_1g_mapping_without_free_eof_transition_framing); };
        remove_held_1g_mapping_without_free_eof(*old(krnl), *krnl, pagetable, va, pg_ptr);
    }
}

/// Drop the mapping `(pagetable_ptr, va)` of the mapped 1G page, which keeps other references.
fn remove_shared_1g_mapping(page: &mut Page, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        old(page).inv(),
        old(page).state is Mapped1g,
        old(page).mappings().contains((pagetable_ptr, va)),
        old(page).ref_count > 1,
    ensures
        final(page).inv(),
        final(page).mappings() == old(page).mappings().remove((pagetable_ptr, va)),
        final(page).ref_count == old(page).ref_count - 1,
        *final(page) == (Page { mappings: final(page).mappings, ref_count: final(page).ref_count, ..*old(page) }),
{
    page.mappings = Ghost(page.mappings().remove((pagetable_ptr, va)));
    page.ref_count = page.ref_count - 1;
    proof { reveal(Page::mappings_va_valid); assert(page.iommu_mappings() == old(page).iommu_mappings()); }
}
}
