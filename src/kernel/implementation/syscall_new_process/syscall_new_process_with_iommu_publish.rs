use vstd::prelude::*;
use crate::*;

verus! {

pub(super) fn publish_staged_process_with_iommu(
    krnl: &mut KernelK,
    source_range: &VaRange4K,
    Ghost(endpoint_exceptions): Ghost<Set<RwLockEndpointPtr>>,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId,
    container_ptr: RwLockContainerPtr,
    parent_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    scheduler_ptr: RwLockSchedulerPtr,
    allocator_ptr: RwLockPageAllocatorPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    source_pagetable_ptr: RwLockPageTableRoot,
    pcid: Pcid,
    process_page_ptr: PagePtr,
    pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr,
    iommu_l4_page_ptr: PagePtr,
    process_page_lock_perm: Tracked<LockPerm>,
    pagetable_page_lock_perm: Tracked<LockPerm>,
    l4_page_lock_perm: Tracked<LockPerm>,
    iommu_table_page_lock_perm: Tracked<LockPerm>,
    iommu_l4_page_lock_perm: Tracked<LockPerm>,
    Tracked(cpu_lock_perm): Tracked<&LockPerm>,
    Tracked(container_lock_perm): Tracked<&LockPerm>,
    pcid_allocator_lock_perm: Tracked<LockPerm>,
    parent_lock_perm: Tracked<LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: (RwLockProcessPtr, RwLockPageTableRoot, RwLockPageTableRoot, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        index_valid(NUM_CPUS, cpu_id),
        source_range.wf(),
        source_range.len > 0,
        source_range.len <= (usize::MAX - 4) / 3,
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).wlocked_by(old(lctx)),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).wlocked_by(old(lctx)),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        pcid_allocator_lock_perm.view().state() is WriteLock,
        pcid_allocator_lock_perm.view().thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.view().lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(parent_ptr).wlocked_by(old(lctx)),
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        parent_lock_perm.view().state() is WriteLock,
        parent_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 6 + 3 * source_range.len,
        old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().wf(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).wlocked_by(old(lctx)),
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        share_mapping_4k_source_range_present(old(krnl), source_pagetable_ptr, source_range),
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
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().wlocked_by(old(lctx)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().wlocked_by(old(lctx)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().wlocked_by(old(lctx)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().wlocked_by(old(lctx)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().wlocked_by(old(lctx)),
        process_page_lock_perm.view().state() is WriteLock && process_page_lock_perm.view().thread_id() == old(lctx).thread_id() && process_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.view().state() is WriteLock && pagetable_page_lock_perm.view().thread_id() == old(lctx).thread_id() && pagetable_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.view().state() is WriteLock && l4_page_lock_perm.view().thread_id() == old(lctx).thread_id() && l4_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().locking_thread()->Write_lock_id,
        iommu_table_page_lock_perm.view().state() is WriteLock && iommu_table_page_lock_perm.view().thread_id() == old(lctx).thread_id() && iommu_table_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().locking_thread()->Write_lock_id,
        iommu_l4_page_lock_perm.view().state() is WriteLock && iommu_l4_page_lock_perm.view().thread_id() == old(lctx).thread_id() && iommu_l4_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom() == set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr), page_ptr2page_index(iommu_table_page_ptr), page_ptr2page_index(iommu_l4_page_ptr)],
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        old(lctx).object_lock_scope(set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr), page_ptr2page_index(iommu_table_page_ptr), page_ptr2page_index(iommu_l4_page_ptr)], set![cpu_id], set![container_ptr], set![parent_ptr], set![current_thread_ptr], endpoint_exceptions, Set::empty(), set![pcid_allocator_ptr], set![source_pagetable_ptr], Set::empty()),
        cpu_objects_unlocked_except(old(krnl).cpu_arr, old(lctx).thread_id(), set![cpu_id]),
        container_objects_unlocked_except(old(krnl).ctn_mp, old(lctx).thread_id(), set![container_ptr]),
        scheduler_objects_unlocked(old(krnl).sched_mp, old(lctx).thread_id()),
        process_objects_unlocked_except(old(krnl).prc_mp, old(lctx).thread_id(), set![parent_ptr]),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![current_thread_ptr]),
        endpoint_objects_unlocked_except(old(krnl).ep_mp, old(lctx).thread_id(), endpoint_exceptions),
        page_objects_unlocked_except(old(krnl).pg_arr, old(lctx).thread_id(), set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr), page_ptr2page_index(iommu_table_page_ptr), page_ptr2page_index(iommu_l4_page_ptr)]),
        pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), set![source_pagetable_ptr]),
        iommu_table_objects_unlocked(old(krnl).it_mp, old(lctx).thread_id()),
        pcid_allocator_objects_unlocked_except(old(krnl).pcid_allc_mp, old(lctx).thread_id(), set![pcid_allocator_ptr]),
        allocator_objects_unlocked(old(krnl).allc_4k_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
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
        mmap_4k_allocation_ready(final(krnl), final(lctx)),
        final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![ret.0], set![current_thread_ptr], endpoint_exceptions, Set::empty(), Set::empty(), set![source_pagetable_ptr, ret.1], set![ret.2]),
        kernel_objects_unlocked_except(final(krnl), final(lctx).thread_id(), set![cpu_id], set![container_ptr], Set::empty(), set![ret.0], set![current_thread_ptr], Set::empty(), endpoint_exceptions, set![source_pagetable_ptr, ret.1], set![ret.2], Set::empty(), Set::empty(), Set::empty(), Set::empty()),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(final(lctx)),
        !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == final(lctx).thread_id(),
        cpu_lock_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).wlocked_by(final(lctx)),
        !final(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        final(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == final(lctx).thread_id(),
        container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.dom().contains(ret.0),
        final(krnl).prc_mp.spec_index(ret.0).wlocked_by(final(lctx)),
        !final(krnl).prc_mp.spec_index(ret.0).being_killed(),
        final(krnl).prc_mp.spec_index(ret.0).view_rodata().view().owning_container == container_ptr,
        final(krnl).prc_mp.spec_index(ret.0).view_rodata().view().pagetable == ret.1,
        final(krnl).prc_mp.spec_index(ret.0).view().iommu_table == Some(ret.2),
        final(krnl).it_mp.dom().contains(ret.2),
        final(krnl).it_mp.spec_index(ret.2).view().is_empty(),
        final(krnl).it_mp.spec_index(ret.2).wlocked_by(final(lctx)),
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).prc_mp.spec_index(ret.0).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(final(lctx)),
        !final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc != ret.0,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1 + 3 * source_range.len,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        source_pagetable_ptr != ret.1,
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).wlocked_by(final(lctx)),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view().proc_ptr == parent_ptr,
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view().wf(),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        share_mapping_4k_source_range_present(final(krnl), source_pagetable_ptr, source_range),
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(ret.1),
        final(krnl).pt_mp.spec_index(ret.1).wlocked_by(final(lctx)),
        final(krnl).pt_mp.spec_index(ret.1).view().proc_ptr == ret.0,
        final(krnl).pt_mp.spec_index(ret.1).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        final(krnl).pt_mp.spec_index(ret.1).view().is_empty(),
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).pt_mp.spec_index(ret.1).locking_thread()->Write_lock_id,
        ret.5.view().state() is WriteLock,
        ret.5.view().thread_id() == final(lctx).thread_id(),
        ret.5.view().lock_id() == final(krnl).it_mp.spec_index(ret.2).locking_thread()->Write_lock_id,
{
    hide(kernel_u_create_process_with_iommu_changed);
    hide(process_add_child_ensures);
    hide(kernel_objects_unlocked_except);
    hide(held_containers_unchanged);
    hide(held_processes_unchanged);
    hide(held_threads_unchanged);
    hide(held_endpoints_unchanged);
    hide(held_schedulers_unchanged);
    hide(held_pcid_allocators_unchanged);
    hide(held_iommu_tables_unchanged);
    hide(held_pages_unchanged);
    hide(held_cpus_unchanged);
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
        assert(uppers.no_duplicates()) by { reveal(process_perms_wf); reveal(process_tree_fields_wf); };
        assert(uppers.len() <= NUM_PAGES) by { reveal(container_process_wf); reveal(per_container_process_tree_wf); reveal(process_tree_wf); reveal(process_uppertree_seq_wf); lemma_kernel_object_ptr_seq_len_bounded(&*krnl, uppers); };
        assert(krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX) by { reveal(process_perms_wf); reveal(process_tree_fields_wf); assert(NUM_PAGES < usize::MAX) by (compute); };
    }
    proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); }
    let (child_ptr, target_pagetable_ptr, iommu_table_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm)) = create_process_with_iommu_from_staged_pages(krnl, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, current_thread_ptr, container_ptr, pcid_allocator_ptr, pcid, Tracked(&mut *lctx), Tracked(&process_page_lock_perm), Tracked(&pagetable_page_lock_perm), Tracked(&l4_page_lock_perm), Tracked(&iommu_table_page_lock_perm), Tracked(&iommu_l4_page_lock_perm), Tracked(&container_lock_perm), Tracked(&parent_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&pcid_allocator_lock_perm));
    proof {
        assert({
            &&& thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![current_thread_ptr])
            &&& krnl.thr_mp.dom().contains(current_thread_ptr)
            &&& krnl.thr_mp.spec_index(current_thread_ptr).wlocked_by(lctx)
            &&& current_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().state is RUNNING
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean()
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1 + 3 * source_range.len
            &&& krnl.pt_mp.dom().contains(target_pagetable_ptr)
            &&& krnl.pt_mp.spec_index(target_pagetable_ptr).wlocked_by(lctx)
            &&& target_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(target_pagetable_ptr).locking_thread()->Write_lock_id
            &&& krnl.pt_mp.spec_index(target_pagetable_ptr).view().proc_ptr == child_ptr
        }) by { reveal(thread_objects_unlocked_except); };
        assert(process_objects_unlocked_except(krnl.prc_mp, lctx.thread_id(), set![parent_ptr, child_ptr])) by { reveal(process_objects_unlocked_except); };
        assert(page_objects_unlocked_except(krnl.pg_arr, lctx.thread_id(), set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr), page_ptr2page_index(iommu_table_page_ptr), page_ptr2page_index(iommu_l4_page_ptr)])) by { reveal(page_objects_unlocked_except); };
        assert(pagetable_objects_unlocked_except(krnl.pt_mp, lctx.thread_id(), set![source_pagetable_ptr].insert(target_pagetable_ptr))) by { reveal(pagetable_objects_unlocked_except); };
        assert(iommu_table_objects_unlocked_except(krnl.it_mp, lctx.thread_id(), set![iommu_table_ptr])) by { reveal(iommu_table_objects_unlocked_except); };
    }

    krnl.wunlock_page(page_ptr2page_index(iommu_l4_page_ptr), Tracked(&mut *lctx), Tracked(iommu_l4_page_lock_perm));
    proof { assert(krnl.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().wlocked_by(lctx) && iommu_table_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().locking_thread()->Write_lock_id) by { reveal(LockedArray::unchanged_except); page_ptr2page_index_injective(); }; }
    krnl.wunlock_page(page_ptr2page_index(iommu_table_page_ptr), Tracked(&mut *lctx), Tracked(iommu_table_page_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(l4_page_ptr), Tracked(&mut *lctx), Tracked(l4_page_lock_perm));
    proof { assert(krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().wlocked_by(lctx) && pagetable_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id) by { reveal(LockedArray::unchanged_except); page_ptr2page_index_injective(); }; }
    krnl.wunlock_page(page_ptr2page_index(pagetable_page_ptr), Tracked(&mut *lctx), Tracked(pagetable_page_lock_perm));
    proof { assert(krnl.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().wlocked_by(lctx) && process_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id) by { reveal(LockedArray::unchanged_except); page_ptr2page_index_injective(); }; }
    krnl.wunlock_page(page_ptr2page_index(process_page_ptr), Tracked(&mut *lctx), Tracked(process_page_lock_perm));
    proof { assert(krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0 && !krnl.prc_mp.spec_index(parent_ptr).being_killed()) by { reveal(process_thread_wf); }; }
    krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
    proof { assert(process_objects_unlocked_except(krnl.prc_mp, lctx.thread_id(), set![child_ptr])) by { reveal(process_objects_unlocked_except); }; }
    krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
    proof {
        assert(krnl.ep_mp == old(krnl).ep_mp && lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map()) by { reveal(typed_lock_maps_removed); reveal(typed_lock_maps_unchanged); };
        assert(lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); reveal(lock_id_set_aligned); reveal(typed_lock_maps_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(cpu_array_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(pagetable_perms_wf); reveal(iommu_table_perms_wf); };
        assert(krnl.it_mp.dom().contains(iommu_table_ptr) && krnl.it_mp.spec_index(iommu_table_ptr).wlocked_by(lctx) && krnl.it_mp.spec_index(iommu_table_ptr).view().is_empty() && iommu_table_lock_perm.lock_id() == krnl.it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id) by { reveal(held_iommu_tables_unchanged); };
        krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
        assert(krnl.it_mp.dom().contains(iommu_table_ptr) && krnl.it_mp.spec_index(iommu_table_ptr).wlocked_by(lctx) && krnl.it_mp.spec_index(iommu_table_ptr).view().is_empty() && iommu_table_lock_perm.lock_id() == krnl.it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id) by { reveal(held_iommu_tables_unchanged); };
        assert(steps.steps.len() == old(steps).steps.len() + 1) by { reveal(record_user_view_change); };
        assert(kernel_u_create_process_with_iommu_changed(steps.steps.spec_index(old(steps).steps.len() as int).old_u, steps.steps.spec_index(old(steps).steps.len() as int).new_u, parent_ptr, child_ptr)) by { reveal(record_user_view_change); };
        assert({
            let created_u = steps.steps.spec_index(old(steps).steps.len() as int).new_u;
            &&& created_u.process_map.dom().contains(parent_ptr)
            &&& created_u.process_map.dom().contains(child_ptr)
            &&& created_u.process_map.spec_index(child_ptr) == kernel_k_to_kernel_u(*krnl).process_map.spec_index(child_ptr)
        }) by { reveal(kernel_u_create_process_with_iommu_changed); reveal(record_user_view_change); reveal(kernel_k_to_kernel_u); reveal(process_iommu_table_match); reveal(held_processes_unchanged); reveal(held_pagetables_unchanged); reveal(held_iommu_tables_unchanged); };
        assert(held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx))) by { reveal(held_endpoints_unchanged); };
    }
    proof {
        assert(krnl.cpu_arr.spec_index(cpu_id).view().wlocked_by(lctx) && cpu_lock_perm.lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id) by { reveal(held_cpus_unchanged); };
        assert(krnl.ctn_mp.spec_index(container_ptr).wlocked_by(lctx) && !krnl.ctn_mp.spec_index(container_ptr).being_killed() && krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr && container_lock_perm.lock_id() == krnl.ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id) by { reveal(held_containers_unchanged); };
        assert(krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { reveal(container_allocator_wf); };
        assert(krnl.prc_mp.dom().contains(child_ptr) && krnl.prc_mp.spec_index(child_ptr).wlocked_by(lctx) && !krnl.prc_mp.spec_index(child_ptr).being_killed() && krnl.prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr && child_lock_perm.lock_id() == krnl.prc_mp.spec_index(child_ptr).locking_thread()->Write_lock_id) by { reveal(held_processes_unchanged); };
        assert(krnl.prc_mp.spec_index(child_ptr).view_rodata().view().pagetable == target_pagetable_ptr && krnl.prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr)) by { reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(held_processes_unchanged); };
        assert(krnl.thr_mp.dom().contains(current_thread_ptr) && krnl.thr_mp.spec_index(current_thread_ptr).wlocked_by(lctx) && current_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id && krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr && krnl.thr_mp.spec_index(current_thread_ptr).view().state is RUNNING) by { reveal(held_threads_unchanged); reveal(LockedArray::unchanged_except); reveal(LockedMap::unchanged_except); };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc != child_ptr) by { reveal(process_add_child_ensures); reveal(process_thread_wf); reveal(process_tree_fields_wf); };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr) by { reveal(LockedArray::unchanged_except); reveal(LockedMap::unchanged_except); };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean() && krnl.thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean() && krnl.thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1 + 3 * source_range.len) by { reveal(LockedArray::unchanged_except); reveal(LockedMap::unchanged_except); };
        assert(krnl.pt_mp.spec_index(source_pagetable_ptr).view().proc_ptr == parent_ptr) by { reveal(process_thread_wf); reveal(process_pagetable_match); reveal(held_threads_unchanged); };
        assert(source_pagetable_ptr != target_pagetable_ptr) by { reveal(process_pagetable_match); };
        assert(krnl.pt_mp.spec_index(source_pagetable_ptr).wlocked_by(lctx) && source_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id) by { reveal(held_pagetables_unchanged); };
        assert(lctx.page_lock_map().dom().is_empty()) by { reveal(typed_lock_maps_removed); page_ptr2page_index_injective(); };
        assert(page_objects_unlocked(krnl.pg_arr, lctx.thread_id())) by { reveal(page_objects_unlocked); reveal(page_objects_unlocked_except); page_ptr2page_index_injective(); };
        assert(allocator_objects_unlocked(krnl.allc_4k_mp, lctx.thread_id())) by { reveal(allocator_objects_unlocked); };
        assert(lctx.holds_no_allocator_locks(PageSize::SZ4k)) by { reveal(LocalContext::holds_no_allocator_locks); reveal(typed_lock_maps_removed); };
        assert(lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by { reveal(LocalContext::holds_no_allocator_locks); reveal(typed_lock_maps_unchanged); reveal(typed_lock_maps_removed); };
        assert(mmap_4k_allocation_ready(krnl, lctx)) by { reveal(mmap_4k_allocation_ready); };
        assert(pagetable_objects_unlocked_except(krnl.pt_mp, lctx.thread_id(), set![source_pagetable_ptr, target_pagetable_ptr])) by { reveal(pagetable_objects_unlocked_except); };
        assert(krnl.pt_mp.dom().contains(source_pagetable_ptr) && krnl.pt_mp.spec_index(source_pagetable_ptr) == old(krnl).pt_mp.spec_index(source_pagetable_ptr)) by { reveal(held_pagetables_unchanged); };
        assert(krnl.pt_mp.spec_index(source_pagetable_ptr).view().wf() && krnl.pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start)) by { source_range.va_range_lemma(); };
        assert(share_mapping_4k_source_range_present(krnl, source_pagetable_ptr, source_range)) by { reveal(share_mapping_4k_source_range_present); reveal(PageTable::wf_mapping_4k); reveal(mapped_4k_page_pagetable_wf); source_range.va_range_lemma(); };
        assert(krnl.pt_mp.dom().contains(target_pagetable_ptr) && krnl.pt_mp.spec_index(target_pagetable_ptr).wlocked_by(lctx) && target_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(target_pagetable_ptr).locking_thread()->Write_lock_id && krnl.pt_mp.spec_index(target_pagetable_ptr).view().proc_ptr == child_ptr) by { reveal(held_pagetables_unchanged); reveal(LockedArray::unchanged_except); reveal(LockedMap::unchanged_except); };
        assert(krnl.pt_mp.spec_index(target_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start)) by { reveal(KernelK::default_pagetable_wf); reveal(LockedArray::unchanged_except); reveal(LockedMap::unchanged_except); source_range.va_range_lemma(); };
        assert(krnl.pt_mp.spec_index(target_pagetable_ptr).view().is_empty()) by { reveal(held_pagetables_unchanged); };
        assert(kernel_objects_unlocked_except(krnl, lctx.thread_id(), set![cpu_id], set![container_ptr], Set::empty(), set![child_ptr], set![current_thread_ptr], Set::empty(), endpoint_exceptions, set![source_pagetable_ptr, target_pagetable_ptr], set![iommu_table_ptr], Set::empty(), Set::empty(), Set::empty(), Set::empty())) by { reveal(kernel_objects_unlocked_except); reveal(cpu_objects_unlocked_except); reveal(container_objects_unlocked_except); reveal(scheduler_objects_unlocked_except); reveal(process_objects_unlocked_except); reveal(thread_objects_unlocked_except); reveal(endpoint_objects_unlocked_except); reveal(page_objects_unlocked_except); reveal(pagetable_objects_unlocked_except); reveal(iommu_table_objects_unlocked_except); reveal(pcid_allocator_objects_unlocked_except); reveal(allocator_objects_unlocked_except); reveal(held_cpus_unchanged); reveal(held_schedulers_unchanged); reveal(held_endpoints_unchanged); reveal(held_iommu_tables_unchanged); page_ptr2page_index_injective(); };
    }
    (child_ptr, target_pagetable_ptr, iommu_table_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm))
}

} // verus!
