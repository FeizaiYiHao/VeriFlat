use vstd::prelude::*;
use crate::*;
use super::share_mapping_4k::*;

verus! {
/// Reads the runtime owner of the page behind source leaf `i` under a transient page write lock and checks it against `target_container`.
pub(super) fn share_mapping_4k_source_owner_check_at(
    krnl: &mut KernelK, source_range: &VaRange4K, i: usize, target_thread: RwLockThreadPtr, target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: bool)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.lock_id_by_index(held_page).major < MAPPED_PAGE_LOCK_MAJOR,
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(krnl).thr_mp.dom().contains(target_thread),
        old(lctx).thread_lock_map().dom().contains(target_thread),
        mmap_4k_quota_thread_container_compatible(old(krnl), old(lctx), target_thread, target_container),
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        old(lctx).pagetable_lock_map().dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        source_range.wf(),
        i < source_range.len,
        old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
        old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))),
        old(steps).snapshot_k() == *old(krnl) ==> final(steps).view() == old(steps).view(),
        final(steps).snapshot_k() == *final(krnl),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        forall|held_cpu_id: CpuId| #![trigger final(lctx).cpu_lock_map().dom().contains(held_cpu_id)] final(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(final(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger final(lctx).page_lock_map().dom().contains(held_page)] final(lctx).page_lock_map().dom().contains(held_page) ==> final(krnl).pg_arr.lock_id_by_index(held_page).major < MAPPED_PAGE_LOCK_MAJOR,
        mmap_4k_quota_thread_container_compatible(final(krnl), final(lctx), target_thread, target_container),
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        share_mapping_4k_source_range_present(final(krnl), source_pagetable, source_range),
        share_mapping_4k_range_owner_compatible_prefix(final(krnl), source_pagetable, target_container, source_range, i as int)
            == share_mapping_4k_range_owner_compatible_prefix(old(krnl), source_pagetable, target_container, source_range, i as int),
        ret == share_mapping_4k_leaf_owner_compatible(final(krnl), source_pagetable, target_container, source_range.view().spec_index(i as int)),
{
    let source_va = source_range.index(i);
    let source_indices = va2index(source_va);
    proof {
        pagetable_perms_wf_map(krnl.pt_mp);
        pagetable_perms_wf_at(krnl.pt_mp, source_pagetable);
        assert({
            &&& spec_index2va(source_indices) == source_va
            &&& krnl.pt_mp.spec_index(source_pagetable).view().spec_resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3) is Some
        }) by { spec_va_4k_index_roundtrip_at(source_va, source_indices.0, source_indices.1, source_indices.2, source_indices.3); };
    }
    let source_entry;
    {
        let source = krnl.pt_mp.borrow_typed(source_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(source_pagetable_lock_perm));
        source_entry = source.resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3).2.unwrap();
    }
    let page_ptr = source_entry.addr;
    let page_index = page_ptr2page_index(page_ptr);
    let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    let page_owner;
    {
        proof { assert(krnl.pg_arr.inv()) by { page_array_wf_map(krnl.pg_arr); }; }
        let page = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_lock_perm));
        page_owner = page.owning_container;
    }
    let page_compatible;
    if page_owner == target_container {
        page_compatible = true;
    } else {
        proof {
            assert({
                &&& container_perms_wf(krnl.ctn_mp)
                &&& container_tree_wf(krnl.rt_ctn, krnl.ctn_mp)
                &&& krnl.ctn_mp.dom().contains(page_owner)
                &&& krnl.ctn_mp.dom().contains(target_container)
            }) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, target_thread); };
        }
        page_compatible = container_tree_check_is_ancestor(krnl.rt_ctn, &krnl.ctn_mp, page_owner, target_container);
    }
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
        };
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        assert({
            &&& krnl.prc_mp.dom().contains(target_process)
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable
        }) by { process_pagetable_match_pagetable_at(krnl.prc_mp, krnl.pt_mp, target_pagetable); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process); };
    }
    page_compatible
}
} // verus!
