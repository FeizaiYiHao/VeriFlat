use vstd::prelude::*;
use crate::*;
use super::move_pool_page_to_cache::move_pool_page_to_cache;

verus! {
/// Moves up to `ALLOCATOR_BATCH` pages from the global pool head into the empty CPU cache, so later
/// allocations on this CPU hit the cache instead of contending on the global-pool lock.
pub fn refill_4k_cache_batch(krnl: &mut KernelK, allocator: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cache_perm: Tracked<&LockPerm>, pool_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).allc_4k_mp.dom().contains(allocator),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().len() == 0,
        old(krnl).allc_4k_mp.spec_index(allocator).global_pool.view().view().len() > 0,
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
        old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
        old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.spec_index(held_page).view().view().orders_below_allocator_locks(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
    ensures
        final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).allc_4k_mp.dom().contains(allocator),
        final(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
        cache_perm.view().lock_id() == final(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        pool_perm.view().lock_id() == final(krnl).allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
        forall|held_cpu_id: CpuId| #![trigger final(lctx).cpu_lock_map().dom().contains(held_cpu_id)] final(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(final(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger final(lctx).page_lock_map().dom().contains(held_page)] final(lctx).page_lock_map().dom().contains(held_page) ==> final(krnl).pg_arr.spec_index(held_page).view().view().orders_below_allocator_locks(),
        forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t) ==> {
            let owner = old(krnl).thr_mp.spec_index(t).view().owning_container;
            &&& final(krnl).ctn_mp.dom().contains(owner)
            &&& final(krnl).ctn_mp.spec_index(owner).view_rodata() == old(krnl).ctn_mp.spec_index(owner).view_rodata()
        },
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
{
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx) && held_threads_unchanged(krnl.thr_mp, krnl.thr_mp, lctx)
        && held_endpoints_unchanged(krnl.ep_mp, krnl.ep_mp, lctx) && held_schedulers_unchanged(krnl.sched_mp, krnl.sched_mp, lctx) && held_pcid_allocators_unchanged(krnl.pcid_allc_mp, krnl.pcid_allc_mp, lctx)
        && held_cpu_sets_unchanged(krnl.cpu_set_mp, krnl.cpu_set_mp, lctx) && held_pages_unchanged(krnl.pg_arr, krnl.pg_arr, lctx) && held_cpus_unchanged(krnl.cpu_arr, krnl.cpu_arr, lctx)
        && held_pagetables_unchanged(krnl.pt_mp, krnl.pt_mp, lctx) && held_iommu_tables_unchanged(krnl.it_mp, krnl.it_mp, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    assert(krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.spec_index(allocator).wf()) by { allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allocator); };
    let pool = krnl.allc_4k_mp.borrow_global_pool_typed(allocator, Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), pool_perm);
    proof { pool.lemma_len_view(); }
    let pool_len = pool.len();
    let target = if pool_len < ALLOCATOR_BATCH { pool_len } else { ALLOCATOR_BATCH };
    let mut moved = 0usize;
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    while moved < target
        invariant
            moved == 0 ==> steps.view() == old(steps).view() && *krnl == *old(krnl) && steps.snapshot_u() == old(steps).snapshot_u(),
            moved > 0 ==> steps.view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
            0 < target <= ALLOCATOR_BATCH,
            target <= old(krnl).allc_4k_mp.spec_index(allocator).global_pool.view().view().len(),
            0 <= moved <= target,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            lctx.cpu_offline_flag_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu_id)] lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger lctx.page_lock_map().dom().contains(held_page)] lctx.page_lock_map().dom().contains(held_page) ==> krnl.pg_arr.spec_index(held_page).view().view().orders_below_allocator_locks(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            moved > 0 ==> steps.snapshot_k() == *krnl,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.view().owners() == steps.snapshot_k().irt.view().owners(),
            krnl.irt.view().iommu_roots() == steps.snapshot_k().irt.view().iommu_roots(),
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
            krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().len() == moved,
            krnl.allc_4k_mp.spec_index(allocator).global_pool.view().view().len() == old(krnl).allc_4k_mp.spec_index(allocator).global_pool.view().view().len() - moved,
            moved > 0 ==> forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t) ==> {
                let owner = old(krnl).thr_mp.spec_index(t).view().owning_container;
                &&& krnl.ctn_mp.dom().contains(owner)
                &&& krnl.ctn_mp.spec_index(owner).view_rodata() == old(krnl).ctn_mp.spec_index(owner).view_rodata()
            },
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_threads_unchanged(old(krnl).thr_mp, krnl.thr_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, krnl.cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx)),
            held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view(), old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
        decreases target - moved,
    {
        assert(krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.spec_index(allocator).wf()) by { allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allocator); };
        let pool = krnl.allc_4k_mp.borrow_global_pool_typed(allocator, Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), pool_perm);
        proof { pool.lemma_len_view(); }
        let (_, page_ptr) = pool.peek_head();
        assert(page_ptr_valid(page_ptr)) by { allocator_free_page_ptrs_wf_global_at(krnl.allc_4k_mp, allocator, page_ptr); };
        let page_index = page_ptr2page_index(page_ptr);
        assert(index_valid(NUM_PAGES, page_index) && krnl.pg_arr.lock_id_by_index(page_index).major == FREE_PAGE_LOCK_MAJOR) by {
            container_allocator_free_4k_page_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, allocator, page_ptr); reveal(LinkedList::wf_value_list); page_ptr_valid_imply_page_index_valid(); seq_skip_lemma::<PagePtr>();
            page_array_wf_at(krnl.pg_arr, page_index);
        };
        let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
        move_pool_page_to_cache(krnl, allocator, cpu_id, page_ptr, Tracked(&mut *lctx), cache_perm, pool_perm, Tracked(&page_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write }); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            if moved != 0 { kernel_snapshot_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&*steps, &*krnl); }
            assert(kernel_k_to_kernel_u(*krnl) == if moved == 0 { kernel_k_to_kernel_u(*old(krnl)) } else { steps.snapshot_u() }) by {
                if moved == 0 {
                    broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
                    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
                }
            };
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
        moved = moved + 1;
    }
}
}
