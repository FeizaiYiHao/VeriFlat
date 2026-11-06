use vstd::prelude::*;
use crate::*;
use super::unmap_4k_reclaim_last_cache::reclaim_last_lock_4k_cache_with_room;
#[cfg(verus_keep_ghost)]
use super::mmap_1g_reclaim_table_page_eof::*;

verus! {
/// Take the table page `pg_ptr` out of the write-held `pagetable` (the L1 page of entry `(l4i, l3i, l2i)` of the L2 page `l2_ptr` when `l1`, else `l2_ptr` itself, under the hidden L3
/// entry `(l4i, l3i)`) and return it through the write-held cache shard `cpu_id` of the 4K allocator `allc_ptr` of its owner, crediting its quota by one.
fn mmap_1g_reclaim_table_page_to_cache(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, pagetable: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, l2_ptr: PageMapPtr,
    pg_ptr: PagePtr, owner: RwLockContainerPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<&LockPerm>,
    Tracked(cache_perm): Tracked<&LockPerm>, Tracked(quota_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        pei_valid(l2i),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l3(l4i, l3i) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l3(l4i, l3i)->0.addr == l2_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(l4i, l3i) is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
        l1 ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_page(l2_ptr).entry_lock(l2i).l1() is Some && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry(l2_ptr, l2i).addr == pg_ptr,
        l1 ==> forall|i1: L1Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, i1)] pei_valid(i1) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, i1) is None,
        !l1 ==> pg_ptr == l2_ptr,
        !l1 ==> forall|i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_page(l2_ptr).entry_lock(i).l1()]
            pei_valid(i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_page(l2_ptr).entry_lock(i).l1() is None,
        !l1 ==> forall|i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, i)] pei_valid(i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, i) is None,
        page_ptr_valid(pg_ptr),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable, table_type: PT_TYPE } }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == owner,
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allc_ptr,
        old(krnl).allc_4k_mp.dom().contains(allc_ptr),
        old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allc_ptr, cpu_id), TypedLockMode::Write),
        cache_perm.state() is WriteLock,
        cache_perm.thread_id() == old(lctx).thread_id(),
        cache_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allc_ptr, TypedLockMode::Write),
        quota_perm.state() is WriteLock,
        quota_perm.thread_id() == old(lctx).thread_id(),
        quota_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allc_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)),
            TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(*old(krnl), *final(krnl), pagetable, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().free_list_node_storage.addr()),
{
    let pg_idx = page_ptr2page_index(pg_ptr);
    proof {
        page_ptr_valid_imply_page_index_valid();
        page_array_wf_at(krnl.pg_arr, pg_idx);
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allc_ptr);
        assert(!krnl.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)) by { allocator_free_4k_pages_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allc_ptr, cpu_id, pg_ptr); };
        lemma_container_allocator_4k_quota_bounded(&*krnl, owner);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        krnl.default_pagetable_wf_at(pagetable);
        let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        c.higher.wf_l4_at(l4i); c.l3_links_l2_wf_at(c.spec_held_l4(l4i)->0.addr, l3i);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        assert(c.page_closure().contains(pg_ptr)) by { if l1 { c.wf_l2_at(l2_ptr, l2i); } };
        held_table_page_under_unresolvable_l3_entry_with_empty_table_record_implies_unreferenced_by_structure_caches(*krnl, pagetable, l4i, l3i, l2i, l1, pg_ptr);
    }
    let ghost pre = *krnl;
    let Tracked(page_4k_perm) = if l1 {
        let Tracked(page_map_perm) = pagetable_map_unlink_hidden_l3_l1_page(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, l4i, l3i, l2i, l2_ptr, pg_ptr, &krnl.pg_arr,
            Tracked(&mut *lctx), Tracked(pagetable_perm));
        page_map_to_page_perm(pg_ptr, Tracked(page_map_perm), &krnl.cpu_tlb, &krnl.cpu_arr, &krnl.pcid_needflush)
    } else {
        pagetable_map_remove_l3_entry(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, l4i, l3i, l2_ptr, &krnl.pg_arr, &krnl.cpu_tlb, &krnl.cpu_arr, &krnl.pcid_needflush,
            Tracked(&mut *lctx), Tracked(pagetable_perm))
    };
    proof {
        if !l1 { assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus =~= Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()); }
    }
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    let (node_addr, node_perm) = page_array_retire_kernel_object_4k_to_cache(&mut krnl.pg_arr, pg_idx, Tracked(page_4k_perm), allc_ptr, cpu_id, Tracked(&*lctx), Tracked(page_perm));
    proof { lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx)); }
    krnl.allc_4k_mp.push_cache_page_typed(allc_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(cache_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allc_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(quota_perm));
        quota.value = quota.value + 1;
    }
    proof {
        assert(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing(pre, *krnl, pagetable, l4i, l3i, l2i, l1, pg_ptr, allc_ptr, cpu_id, node_addr)) by {
            reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
        };
        mmap_1g_reclaim_table_page_to_cache_eof(pre, *krnl, pagetable, l4i, l3i, l2i, l1, pg_ptr, owner, allc_ptr, cpu_id, node_addr);
    }
}

/// Free the table page `pg_ptr` of the write-held `pagetable` under the hidden, flushed L3 entry `(l4i, l3i)` whose L2 page is `l2_ptr`: the L1 page of entry `l2i` when `l1`, else `l2_ptr` itself. Lock the page, its owner's 4K cache shard `cpu_id`
/// (draining a full shard first) and quota, return the page to the cache, credit the quota by one, and unlock. The credit is the one recorded step; returns the owner and the state and local context the step starts from.
pub fn mmap_1g_reclaim_table_page(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1: bool, l2_ptr: PageMapPtr, pg_ptr: PagePtr, cpu_id: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(pagetable_perm): Tracked<&LockPerm>,
) -> (ret: (RwLockContainerPtr, Ghost<KernelK>, Ghost<LocalContext>))
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        pei_valid(l2i),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l3(l4i, l3i) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l3(l4i, l3i)->0.addr == l2_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(l4i, l3i) is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
        l1 ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_page(l2_ptr).entry_lock(l2i).l1() is Some && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry(l2_ptr, l2i).addr == pg_ptr,
        l1 ==> forall|i1: L1Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, i1)] pei_valid(i1) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, i1) is None,
        !l1 ==> pg_ptr == l2_ptr,
        !l1 ==> forall|i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_page(l2_ptr).entry_lock(i).l1()]
            pei_valid(i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_page(l2_ptr).entry_lock(i).l1() is None,
        !l1 ==> forall|i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, i)] pei_valid(i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, i) is None,
    ensures
        final(steps).view().len() == old(steps).view().len() + 1,
        final(steps).view().drop_last() == old(steps).view(),
        final(steps).view().last().old_u == kernel_k_to_kernel_u(ret.1@),
        kernel_u_container_quota_4k_increased(final(steps).view().last().old_u, final(steps).view().last().new_u, ret.0),
        ret.1@.inv(),
        typed_lock_maps_aligned(&ret.1@, &ret.2@),
        ret.2@.cpu_lock_map() == old(lctx).cpu_lock_map(),
        ret.2@.thread_lock_map() == old(lctx).thread_lock_map(),
        ret.2@.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        held_cpus_unchanged(old(krnl).cpu_arr, ret.1@.cpu_arr, old(lctx)),
        held_threads_unchanged(old(krnl).thrd_mp, ret.1@.thrd_mp, old(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
        ret.0 == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container,
        ret.0 == old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view_rodata().view().owning_container,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_pagetables_unchanged_except(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx), set![pagetable]),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().cr3 == old(krnl).pt_mp.spec_index(pagetable).view().cr3,
        final(krnl).pt_mp.spec_index(pagetable).view().pcid == old(krnl).pt_mp.spec_index(pagetable).view().pcid,
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr,
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).page_closure() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).page_closure().remove(pg_ptr),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks,
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(l4i, l3i) is None,
        forall|i4: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(i4)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(i4) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(i4),
        forall|i4: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l4(i4)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l4(i4) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l4(i4),
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l3(i4, i3)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (l1 || (i4, i3) != (l4i, l3i))
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l3(i4, i3) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l3(i4, i3),
        !l1 ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l3(l4i, l3i) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l2(i4, i3, i2)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && (!l1 || (i4, i3, i2) != (l4i, l3i, l2i))
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l2(i4, i3, i2) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l2(i4, i3, i2),
        l1 ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l2(l4i, l3i, l2i) is None,
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2),
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(i4, i3)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(i4, i3) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(i4, i3),
{
    proof {
        let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        assert(c.page_closure().contains(pg_ptr)) by {
            c.higher.wf_l4_at(l4i); c.l3_links_l2_wf_at(c.spec_held_l4(l4i)->0.addr, l3i);
            if l1 { c.wf_l2_at(l2_ptr, l2i); }
        };
        pagetable_pages_wf_closure_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, pg_ptr);
        page_ptr_valid_imply_page_index_valid();
        process_object_pages_owner_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.it_mp, krnl.pg_arr, page_ptr2page_index(pg_ptr));
    }
    let pg_idx = page_ptr2page_index(pg_ptr);
    let Tracked(page_perm) = krnl.wlock_page(pg_idx, Tracked(&mut *lctx));
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx); }
    let owner = krnl.pg_arr.borrow_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm)).owning_container;
    proof {
        assert(krnl.ctn_mp.dom().contains(owner)) by { container_owned_pages_wf_backward_at(krnl.ctn_mp, krnl.pg_arr, pg_idx); };
        container_perms_wf_at(krnl.ctn_mp, owner);
    }
    let allc_ptr = krnl.ctn_mp.borrow_rodata(owner).borrow().allocator_ptr_4k;
    proof {
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        steps.rebase_snapshot_k_if_unchanged(&*krnl);
    }
    let ghost cache_pre = *krnl;
    let Tracked(cache_perm) = reclaim_last_lock_4k_cache_with_room(krnl, allc_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps));
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
    }
    let ghost mid = *krnl;
    let ghost mid_lctx = *lctx;
    proof {
        assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == whole_pagetable(cache_pre.pt_mp, cache_pre.pt_lower.view(), pagetable));
        page_array_wf_at(krnl.pg_arr, pg_idx);
        assert(krnl.ctn_mp.dom().contains(owner)) by { container_owned_pages_wf_backward_at(krnl.ctn_mp, krnl.pg_arr, pg_idx); };
    }
    let Tracked(quota_perm) = krnl.wlock_allocator_quota_4k(allc_ptr, Tracked(&mut *lctx));
    let ghost helper_pre = *krnl;
    mmap_1g_reclaim_table_page_to_cache(krnl, Tracked(&mut *lctx), pagetable, l4i, l3i, l2i, l1, l2_ptr, pg_ptr, owner, allc_ptr, cpu_id, Tracked(pagetable_perm), Tracked(&page_perm),
        Tracked(&cache_perm), Tracked(&quota_perm));
    proof { reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing); }
    krnl.wunlock_allocator_quota_4k(allc_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
    krnl.wunlock_allocator_cache_4k(allc_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
    krnl.wunlock_page(pg_idx, Tracked(&mut *lctx), Tracked(page_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            assert(lctx.page_lock_map() =~= old(lctx).page_lock_map() && lctx.allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map()
                && lctx.allocator_quota_4k_lock_map() =~= old(lctx).allocator_quota_4k_lock_map());
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(krnl.pt_lower.view() =~= steps.snapshot_k().pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
        assert(whole_pagetable(helper_pre.pt_mp, helper_pre.pt_lower.view(), pagetable) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable));
        assert(helper_pre.pt_mp.spec_index(pagetable) == old(krnl).pt_mp.spec_index(pagetable));
        reveal(mmap_1g_reclaim_table_page_to_cache_eof_transition_framing);
        kernel_page_freed_to_owner_quota_implies_u_step(&steps.snapshot_k(), &*krnl, false, pagetable, owner, allc_ptr, owner);
        assert(steps.snapshot_k() == mid);
        krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
    }
    (owner, Ghost(mid), Ghost(mid_lctx))
}
}
