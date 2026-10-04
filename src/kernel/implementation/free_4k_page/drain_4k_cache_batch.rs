use vstd::prelude::*;
use crate::*;
use super::move_cache_page_to_pool::move_cache_page_to_pool;

verus! {
pub fn drain_4k_cache_batch(krnl: &mut KernelK, allocator: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cache_perm: Tracked<&LockPerm>, pool_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).allc_4k_mp.dom().contains(allocator),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().len() >= ALLOCATOR_BATCH,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator, cpu_id), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_4k_lock_map(), allocator, TypedLockMode::Write),
        cache_perm.view().state() is WriteLock,
        cache_perm.view().thread_id() == old(lctx).thread_id(),
        cache_perm.view().lock_id() == old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        pool_perm.view().state() is WriteLock,
        pool_perm.view().thread_id() == old(lctx).thread_id(),
        pool_perm.view().lock_id() == old(krnl).allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.lock_id_by_index(held_page).major < FREE_PAGE_LOCK_MAJOR,
    ensures
        final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).allc_4k_mp.dom().contains(allocator),
        final(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().len() == old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().len() - ALLOCATOR_BATCH,
        final(krnl).allc_4k_mp.spec_index(allocator).global_pool.view().view().len() == old(krnl).allc_4k_mp.spec_index(allocator).global_pool.view().view().len() + ALLOCATOR_BATCH,
        cache_perm.view().lock_id() == final(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        pool_perm.view().lock_id() == final(krnl).allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
        forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] #![trigger final(krnl).pg_arr.spec_index(p)] old(lctx).page_lock_map().dom().contains(p) ==> {
            let owner = old(krnl).pg_arr.spec_index(p).view().view().owning_container;
            &&& final(krnl).ctn_mp.dom().contains(owner)
            &&& final(krnl).ctn_mp.spec_index(owner).view_rodata() == old(krnl).ctn_mp.spec_index(owner).view_rodata()
        },
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
{
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx) && held_threads_unchanged(krnl.thr_mp, krnl.thr_mp, lctx) && held_pages_unchanged(krnl.pg_arr, krnl.pg_arr, lctx) && held_cpus_unchanged(krnl.cpu_arr, krnl.cpu_arr, lctx) && held_pagetables_unchanged(krnl.pt_mp, krnl.pt_mp, lctx) && held_iommu_tables_unchanged(krnl.it_mp, krnl.it_mp, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    assert(forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> krnl.ctn_mp.dom().contains(old(krnl).pg_arr.spec_index(p).view().view().owning_container)) by { reveal(container_page_owner_wf); };
    let mut moved = 0usize;
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    while moved < ALLOCATOR_BATCH
        invariant
            moved == 0 ==> steps.view() == old(steps).view() && *krnl == *old(krnl) && steps.snapshot_u() == old(steps).snapshot_u(),
            moved > 0 ==> steps.view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            0 <= moved <= ALLOCATOR_BATCH,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            lctx.cpu_offline_flag_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu_id)] lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger lctx.page_lock_map().dom().contains(held_page)] lctx.page_lock_map().dom().contains(held_page) ==> krnl.pg_arr.lock_id_by_index(held_page).major < FREE_PAGE_LOCK_MAJOR,
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            moved > 0 ==> steps.snapshot_k() == *krnl,
            steps.nonlock_view() == old(steps).nonlock_view(),
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.owners() == steps.snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == steps.snapshot_k().irt.iommu_roots(),
            krnl.cpu_tlb.view() == steps.snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
            index_valid(NUM_CPUS, cpu_id),
            krnl.allc_4k_mp.dom().contains(allocator),
            typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (allocator, cpu_id), TypedLockMode::Write),
            typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allocator, TypedLockMode::Write),
            cache_perm.view().state() is WriteLock,
            cache_perm.view().thread_id() == lctx.thread_id(),
            cache_perm.view().lock_id() == krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            pool_perm.view().state() is WriteLock,
            pool_perm.view().thread_id() == lctx.thread_id(),
            pool_perm.view().lock_id() == krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().len() >= ALLOCATOR_BATCH,
            krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().len() == old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().len() - moved,
            krnl.allc_4k_mp.spec_index(allocator).global_pool.view().view().len() == old(krnl).allc_4k_mp.spec_index(allocator).global_pool.view().view().len() + moved,
        forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] #![trigger krnl.pg_arr.spec_index(p)] old(lctx).page_lock_map().dom().contains(p) ==> {
            let owner = old(krnl).pg_arr.spec_index(p).view().view().owning_container;
            &&& krnl.ctn_mp.dom().contains(owner)
            &&& krnl.ctn_mp.spec_index(owner).view_rodata() == old(krnl).ctn_mp.spec_index(owner).view_rodata()
        },
        held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, krnl.thr_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
        decreases ALLOCATOR_BATCH - moved,
    {
        assert(krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.spec_index(allocator).wf()) by { reveal(allocator_perms_wf); };
        let cache = krnl.allc_4k_mp.borrow_cache_typed(allocator, cpu_id, Ghost(lctx.allocator_cache_4k_lock_map()), Tracked(&*lctx), cache_perm);
        assert(cache.linked_list.len() > 0) by { cache.linked_list.lemma_len_view(); };
        let (_, page_ptr) = cache.linked_list.peek_head();
        assert(page_ptr_valid(page_ptr)) by { reveal(allocator_free_page_ptrs_wf); };
        let page_index = page_ptr2page_index(page_ptr);
        assert(page_ptr_valid(page_ptr) && index_valid(NUM_PAGES, page_index) && krnl.pg_arr.lock_id_by_index(page_index).major == FREE_PAGE_LOCK_MAJOR) by { reveal(allocator_free_page_ptrs_wf); reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(page_array_wf); reveal(LinkedList::wf_value_list); page_ptr_valid_imply_page_index_valid(); };
        let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
        move_cache_page_to_pool(krnl, allocator, cpu_id, page_ptr, Tracked(&mut *lctx), cache_perm, pool_perm, Tracked(&page_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write }); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            use_type_invariant(&*steps);
            assert(kernel_k_to_kernel_u(*krnl) == if moved == 0 { kernel_k_to_kernel_u(*old(krnl)) } else { steps.snapshot_u() }) by {
                if moved == 0 {
                    broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
                    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
                } else { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl); }
            };
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            assert(forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> krnl.ctn_mp.dom().contains(old(krnl).pg_arr.spec_index(p).view().view().owning_container)) by { reveal(container_page_owner_wf); };

        }
        moved = moved + 1;
    }
}
}
