use vstd::prelude::*;
use vstd::assert_sets_equal;
use crate::*;
use super::allocate_free_4k_impl_base::allocate_free_4k_page;

verus! {
pub open spec fn page_ptrs_to_indices(pages: Seq<PagePtr>) -> Set<PageIndex> {
    pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set()
}

pub open spec fn allocated_4k_page_lock_perms_wf(
    perms: Map<PagePtr, LockPerm>, krnl: &KernelK, lctx: &LocalContext, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
) -> bool {
    forall|page_ptr: PagePtr|
        #![trigger perms.dom().contains(page_ptr)]
        perms.dom().contains(page_ptr) ==> {
            &&& page_ptr_valid(page_ptr)
            &&& perms.spec_index(page_ptr).state() is WriteLock
            &&& perms.spec_index(page_ptr).thread_id() == lctx.thread_id()
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Owned4k { thread_ptr }
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
            &&& perms.spec_index(page_ptr).lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
        }
}

pub fn allocate_free_4k_pages<const N: usize>(
    krnl: &mut KernelK, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (ArrayVec<PagePtr, N>, Tracked<Map<PagePtr, LockPerm>>))
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= N,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == if N == 0 { old(steps).view() }
            else { record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))) },
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        ret.0.wf(),
        ret.0.len() == N,
        ret.0.view().no_duplicates(),
        ret.1.view().dom() == ret.0.view().to_set(),
        allocated_4k_page_lock_perms_wf(ret.1.view(), final(krnl), final(lctx), thread_ptr, container_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
        final(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq,
        final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress == old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress,
        final(krnl).thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(ret.0.view().to_set()),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
            temp_alloc_cache_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            ..old(krnl).thr_mp.spec_index(thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
        final(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m,
        final(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g,
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
        final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
        thread_effective_quota_4k(final(krnl).thr_mp.spec_index(thread_ptr)) == thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) - N,
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(ret.0.view())),
        forall|held_page: PageIndex| #![trigger final(lctx).page_lock_map().dom().contains(held_page)] final(lctx).page_lock_map().dom().contains(held_page) ==> final(krnl).pg_arr.lock_id_by_index(held_page).major < ALLOCATOR_CACHE_MAJOR,
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        N > 0 ==> final(steps).snapshot_k() == *final(krnl),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        final(krnl).irt.owners() == final(steps).snapshot_k().irt.owners(),
        final(krnl).irt.iommu_roots() == final(steps).snapshot_k().irt.iommu_roots(),
        final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
        final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
{

    let mut pages = ArrayVec::<PagePtr, N>::new();
    let tracked mut page_lock_perms: Map<PagePtr, LockPerm> = Map::tracked_empty();
    let mut i: usize = 0;
    proof {
        broadcast use group_held_objects_unchanged_transitive;
        assert(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().to_set())) by { vstd::set::axiom_set_ext_equal(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(), old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().to_set())); };
    }
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    assert(krnl.ctn_mp.dom().contains(container_ptr)) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); };
    while i < N
        invariant
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            i == 0 ==> *krnl == *old(krnl) && steps.view() == old(steps).view() && steps.snapshot_u() == old(steps).snapshot_u(),
            i > 0 ==> steps.view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
            krnl.inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            pages.wf(),
            pages.len() == i,
            pages.view().no_duplicates(),
            page_lock_perms.dom() == pages.view().to_set(),
            allocated_4k_page_lock_perms_wf(page_lock_perms, &*krnl, &*lctx, thread_ptr, container_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == false,
            krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq,
            krnl.thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress == old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress,
            krnl.thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().to_set()),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                temp_alloc_cache_4k: krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
                ..old(krnl).thr_mp.spec_index(thread_ptr).view()
            }),
            krnl.thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            krnl.thr_mp.spec_index(thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m,
            krnl.thr_mp.spec_index(thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g,
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
            thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) == thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) - i,
            thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) >= N - i,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == lctx.thread_id(),
            thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(pages.view())),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_MAJOR),
            held_threads_unchanged_except(old(krnl).thr_mp, krnl.thr_mp, old(lctx), set![thread_ptr]),
            i > 0 ==> steps.snapshot_k() == *krnl,
            steps.nonlock_view() == old(steps).nonlock_view(),
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.owners() == steps.snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == steps.snapshot_k().irt.iommu_roots(),
            krnl.cpu_tlb.view() == steps.snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            krnl.ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, krnl.cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            i <= N,
        decreases N - i,
    {
        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); }; }
        proof { assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; }; }
        proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }; }
        proof {
            assert(lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(pages.view().push(page_ptr)))) by {
                seq_push_lemma::<PagePtr>();
                assert_sets_equal!(lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(pages.view().push(page_ptr))), page_index => {
                    broadcast use Seq::lemma_push_map_commute;
                    pages.view().map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set_ensures();
                    pages.view().map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).push(page_ptr2page_index(page_ptr)).to_set_ensures();
                });
            };
            assert(!pages.view().contains(page_ptr)) by { pages.view().to_set_ensures(); };
            assert(page_lock_perms.insert(page_ptr, page_lock_perm).dom() == pages.view().push(page_ptr).to_set()) by {
                assert_sets_equal!(page_lock_perms.insert(page_ptr, page_lock_perm).dom() == pages.view().push(page_ptr).to_set(), x => { seq_push_lemma::<PagePtr>(); pages.view().to_set_ensures(); pages.view().push(page_ptr).to_set_ensures(); });
            };
            assert(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().push(page_ptr).to_set())) by {
                assert_sets_equal!(old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().to_set()).insert(page_ptr) == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().push(page_ptr).to_set()), x => { seq_push_lemma::<PagePtr>(); pages.view().to_set_ensures(); pages.view().push(page_ptr).to_set_ensures(); });
            };
            assert(allocated_4k_page_lock_perms_wf(page_lock_perms.insert(page_ptr, page_lock_perm), &*krnl, &*lctx, thread_ptr, container_ptr)) by { page_ptr2page_index_injective(); };
            page_lock_perms.tracked_insert(page_ptr, page_lock_perm);
        }
        pages.push_unique(page_ptr);
        i = i + 1;
    }
    (pages, Tracked(page_lock_perms))
}
}
