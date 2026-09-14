use vstd::prelude::*;
use crate::*;

verus! {
pub(super) fn publish_staged_process_with_iommu(krnl: &mut KernelK, Ghost(endpoint_exceptions): Ghost<Set<RwLockEndpointPtr>>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, container_ptr: RwLockContainerPtr, parent_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr, allocator_ptr: RwLockPageAllocatorPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, source_pagetable_ptr: RwLockPageTableRoot, pcid: Pcid, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr, iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, process_page_lock_perm: Tracked<LockPerm>, pagetable_page_lock_perm: Tracked<LockPerm>, l4_page_lock_perm: Tracked<LockPerm>, iommu_table_page_lock_perm: Tracked<LockPerm>, iommu_l4_page_lock_perm: Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<&LockPerm>, Tracked(container_lock_perm): Tracked<&LockPerm>, pcid_allocator_lock_perm: Tracked<LockPerm>, parent_lock_perm: Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>) -> (ret: (RwLockProcessPtr, RwLockPageTableRoot, RwLockPageTableRoot, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        pcid_allocator_lock_perm.view().state() is WriteLock,
        pcid_allocator_lock_perm.view().thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.view().lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        parent_lock_perm.view().state() is WriteLock,
        parent_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 5,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().wf(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        page_ptr_valid(process_page_ptr) && page_ptr_valid(pagetable_page_ptr) && page_ptr_valid(l4_page_ptr) && page_ptr_valid(iommu_table_page_ptr) && page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr && process_page_ptr != l4_page_ptr && process_page_ptr != iommu_table_page_ptr && process_page_ptr != iommu_l4_page_ptr
            && pagetable_page_ptr != l4_page_ptr && pagetable_page_ptr != iommu_table_page_ptr && pagetable_page_ptr != iommu_l4_page_ptr
            && l4_page_ptr != iommu_table_page_ptr && l4_page_ptr != iommu_l4_page_ptr && iommu_table_page_ptr != iommu_l4_page_ptr,
        !old(krnl).prc_mp.dom().contains(process_page_ptr),
        !old(krnl).pt_mp.dom().contains(pagetable_page_ptr),
        !old(krnl).it_mp.dom().contains(iommu_table_page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(iommu_table_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(iommu_l4_page_ptr), TypedLockMode::Write),
        process_page_lock_perm.view().state() is WriteLock && process_page_lock_perm.view().thread_id() == old(lctx).thread_id() && process_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.view().state() is WriteLock && pagetable_page_lock_perm.view().thread_id() == old(lctx).thread_id() && pagetable_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.view().state() is WriteLock && l4_page_lock_perm.view().thread_id() == old(lctx).thread_id() && l4_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().locking_thread()->Write_lock_id,
        iommu_table_page_lock_perm.view().state() is WriteLock && iommu_table_page_lock_perm.view().thread_id() == old(lctx).thread_id() && iommu_table_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().locking_thread()->Write_lock_id,
        iommu_l4_page_lock_perm.view().state() is WriteLock && iommu_l4_page_lock_perm.view().thread_id() == old(lctx).thread_id() && iommu_l4_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom() == set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr), page_ptr2page_index(iommu_table_page_ptr), page_ptr2page_index(iommu_l4_page_ptr)],
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr), page_ptr2page_index(iommu_table_page_ptr), page_ptr2page_index(iommu_l4_page_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= endpoint_exceptions,
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom() =~= set![pcid_allocator_ptr],
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, ret.1, final(krnl).pt_mp.spec_index(ret.1).view()),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()) ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, source_pagetable_ptr, final(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(steps).steps.len() == old(steps).steps.len() + 1,
        final(steps).steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        kernel_u_create_process_with_iommu_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, parent_ptr, ret.0),
        final(steps).steps.last().new_u.process_map.dom().contains(parent_ptr),
        final(steps).steps.last().new_u.process_map.dom().contains(ret.0),
        final(steps).steps.last().new_u.process_map.spec_index(ret.0) == kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(ret.0),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        final(lctx).container_lock_map().dom() =~= set![container_ptr],
        final(lctx).process_lock_map().dom() =~= set![ret.0],
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        final(lctx).endpoint_lock_map().dom() =~= endpoint_exceptions,
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, ret.1],
        final(lctx).iommu_table_lock_map().dom() =~= set![ret.2],
        final(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        final(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        final(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        final(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        final(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        final(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        final(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        final(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.thread_id() == final(lctx).thread_id(),
        cpu_lock_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.dom().contains(container_ptr),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        !final(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        final(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        container_lock_perm.thread_id() == final(lctx).thread_id(),
        container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.dom().contains(ret.0),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), ret.0, TypedLockMode::Write),
        !final(krnl).prc_mp.spec_index(ret.0).being_killed(),
        final(krnl).prc_mp.spec_index(ret.0).view_rodata().view().owning_container == container_ptr,
        final(krnl).prc_mp.spec_index(ret.0).view_rodata().view().pagetable == ret.1,
        final(krnl).prc_mp.spec_index(ret.0).view().iommu_table == Some(ret.2),
        final(krnl).it_mp.dom().contains(ret.2),
        final(krnl).it_mp.spec_index(ret.2).view().is_empty(),
        typed_lock_map_contains_mode(final(lctx).iommu_table_lock_map(), ret.2, TypedLockMode::Write),
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).prc_mp.spec_index(ret.0).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc != ret.0,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 5,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        source_pagetable_ptr != ret.1,
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view().proc_ptr == parent_ptr,
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view().wf(),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).view(),
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(ret.1),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), ret.1, TypedLockMode::Write),
        final(krnl).pt_mp.spec_index(ret.1).view().proc_ptr == ret.0,
        final(krnl).pt_mp.spec_index(ret.1).view().kernel_l4_end == old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(ret.1).view().is_empty(),
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).pt_mp.spec_index(ret.1).locking_thread()->Write_lock_id,
        ret.5.view().state() is WriteLock,
        ret.5.view().thread_id() == final(lctx).thread_id(),
        ret.5.view().lock_id() == final(krnl).it_mp.spec_index(ret.2).locking_thread()->Write_lock_id,
{
    hide(held_schedulers_unchanged);
    hide(held_pcid_allocators_unchanged);
    hide(held_pages_unchanged);
    let tracked mut pcid_allocator_lock_perm = pcid_allocator_lock_perm.get();
    let tracked mut parent_lock_perm = parent_lock_perm.get();
    let tracked process_page_lock_perm = process_page_lock_perm.get();
    let tracked pagetable_page_lock_perm = pagetable_page_lock_perm.get();
    let tracked l4_page_lock_perm = l4_page_lock_perm.get();
    let tracked iommu_table_page_lock_perm = iommu_table_page_lock_perm.get();
    let tracked iommu_l4_page_lock_perm = iommu_l4_page_lock_perm.get();
    proof {
        assert(krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().contains(current_thread_ptr) && krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); };
        let uppers = krnl.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
        assert(uppers.no_duplicates()) by { reveal(process_perms_wf); };
        assert(uppers.len() <= NUM_PAGES) by { reveal(container_process_wf); reveal(per_container_process_tree_wf);  reveal(process_uppertree_seq_wf); lemma_kernel_object_ptr_seq_len_bounded(&*krnl, uppers); };
        assert(krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX) by { reveal(process_perms_wf);  assert(NUM_PAGES < usize::MAX) by (compute); };
    }
    proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); }
    let (child_ptr, target_pagetable_ptr, iommu_table_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm)) = create_process_with_iommu_from_staged_pages(krnl, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, current_thread_ptr, container_ptr, pcid_allocator_ptr, pcid, Tracked(&mut *lctx), Tracked(&process_page_lock_perm), Tracked(&pagetable_page_lock_perm), Tracked(&l4_page_lock_perm), Tracked(&iommu_table_page_lock_perm), Tracked(&iommu_l4_page_lock_perm), Tracked(&container_lock_perm), Tracked(&parent_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&pcid_allocator_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(iommu_l4_page_ptr), Tracked(&mut *lctx), Tracked(iommu_l4_page_lock_perm));
    proof { assert(typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(iommu_table_page_ptr), TypedLockMode::Write) && iommu_table_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().locking_thread()->Write_lock_id) by { page_ptr2page_index_injective(); }; }
    krnl.wunlock_page(page_ptr2page_index(iommu_table_page_ptr), Tracked(&mut *lctx), Tracked(iommu_table_page_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(l4_page_ptr), Tracked(&mut *lctx), Tracked(l4_page_lock_perm));
    proof { assert(typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(pagetable_page_ptr), TypedLockMode::Write) && pagetable_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id) by { page_ptr2page_index_injective(); }; }
    krnl.wunlock_page(page_ptr2page_index(pagetable_page_ptr), Tracked(&mut *lctx), Tracked(pagetable_page_lock_perm));
    proof { assert(typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(process_page_ptr), TypedLockMode::Write) && process_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id) by { page_ptr2page_index_injective(); }; }
    krnl.wunlock_page(page_ptr2page_index(process_page_ptr), Tracked(&mut *lctx), Tracked(process_page_lock_perm));
    proof { assert(krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0 && !krnl.prc_mp.spec_index(parent_ptr).being_killed()) by { reveal(process_thread_wf); }; }
    krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
    krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
    proof {
        assert(lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); };
        krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
        assert({
            let created_u = steps.steps.spec_index(old(steps).steps.len() as int).new_u;
            &&& created_u.process_map.dom().contains(parent_ptr)
            &&& created_u.process_map.dom().contains(child_ptr)
            &&& created_u.process_map.spec_index(child_ptr) == kernel_k_to_kernel_u(*krnl).process_map.spec_index(child_ptr)
        }) by { reveal(process_iommu_table_match); };
    }
    proof {
        assert(krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { reveal(container_allocator_wf); };
        assert(krnl.prc_mp.spec_index(child_ptr).view_rodata().view().pagetable == target_pagetable_ptr && krnl.prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr)) by { reveal(process_pagetable_match); reveal(process_iommu_table_match); };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc != child_ptr) by { reveal(process_thread_wf); };
        assert(krnl.pt_mp.spec_index(source_pagetable_ptr).view().proc_ptr == parent_ptr) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
        assert(source_pagetable_ptr != target_pagetable_ptr) by { reveal(process_pagetable_match); };
        assert(krnl.pt_mp.spec_index(target_pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end) by { reveal(KernelK::default_pagetable_wf); };
        assert(lctx.page_lock_map().dom().is_empty()) by { page_ptr2page_index_injective(); };
        assert(lctx.holds_no_allocator_locks(PageSize::SZ4k)) by { reveal(LocalContext::holds_no_allocator_locks); };
        assert(lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by { reveal(LocalContext::holds_no_allocator_locks); };
    }
    proof { assert(pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, target_pagetable_ptr, krnl.pt_mp.spec_index(target_pagetable_ptr).view())) by { reveal(tlb_wf_spec); }; }
    (child_ptr, target_pagetable_ptr, iommu_table_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm))
}

}
