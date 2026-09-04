use vstd::prelude::*;
use crate::*;

verus! {

/// User-view change predicate for publishing a process with an empty page table.
pub open spec fn kernel_u_create_process_changed(
    old_u: KernelU,
    new_u: KernelU,
    parent_ptr: RwLockProcessPtr,
    child_ptr: RwLockProcessPtr,
) -> bool {
    let child = new_u.process_map.spec_index(child_ptr);
    &&& new_u.cpu_array == old_u.cpu_array
    &&& old_u.process_map.dom().contains(parent_ptr)
    &&& !old_u.process_map.dom().contains(child_ptr)
    &&& new_u.process_map.dom() == old_u.process_map.dom().insert(child_ptr)
    &&& child.pagetable.mapping_4k.is_empty()
    &&& child.pagetable.mapping_2m.is_empty()
    &&& child.pagetable.mapping_1g.is_empty()
    &&& child.iommu_table is None
    &&& child.quota_4k == 0
    &&& child.quota_2m == 0
    &&& child.quota_1g == 0
    &&& child.parent == Some(parent_ptr)
    &&& child.children.len() == 0
    &&& child.depth == old_u.process_map.spec_index(parent_ptr).depth + 1
    &&& child.uppertree_seq == old_u.process_map.spec_index(parent_ptr).uppertree_seq.push(parent_ptr)
    &&& child.subtree_set.is_empty()
    &&& child.owned_threads.len() == 0
    &&& !child.killed
    &&& forall|p: RwLockProcessPtr|
        #![trigger new_u.process_map.spec_index(p)]
        old_u.process_map.dom().contains(p) ==> {
            &&& new_u.process_map.spec_index(p).pagetable == old_u.process_map.spec_index(p).pagetable
            &&& new_u.process_map.spec_index(p).iommu_table == old_u.process_map.spec_index(p).iommu_table
            &&& new_u.process_map.spec_index(p).quota_4k == old_u.process_map.spec_index(p).quota_4k
            &&& new_u.process_map.spec_index(p).quota_2m == old_u.process_map.spec_index(p).quota_2m
            &&& new_u.process_map.spec_index(p).quota_1g == old_u.process_map.spec_index(p).quota_1g
            &&& new_u.process_map.spec_index(p).parent == old_u.process_map.spec_index(p).parent
            &&& new_u.process_map.spec_index(p).depth == old_u.process_map.spec_index(p).depth
            &&& new_u.process_map.spec_index(p).uppertree_seq == old_u.process_map.spec_index(p).uppertree_seq
            &&& new_u.process_map.spec_index(p).owned_threads == old_u.process_map.spec_index(p).owned_threads
            &&& new_u.process_map.spec_index(p).killed == old_u.process_map.spec_index(p).killed
            &&& p == parent_ptr ==> new_u.process_map.spec_index(p).children == old_u.process_map.spec_index(p).children.push(child_ptr)
            &&& p != parent_ptr ==> new_u.process_map.spec_index(p).children == old_u.process_map.spec_index(p).children
            &&& child.uppertree_seq.contains(p) ==> new_u.process_map.spec_index(p).subtree_set == old_u.process_map.spec_index(p).subtree_set.insert(child_ptr)
            &&& !child.uppertree_seq.contains(p) ==> new_u.process_map.spec_index(p).subtree_set == old_u.process_map.spec_index(p).subtree_set
        }
}

pub fn create_process_from_staged_pages(
    krnl: &mut KernelK,
    process_page_ptr: PagePtr,
    pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr,
    parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    pcid: Pcid,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(process_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<&LockPerm>,
    Tracked(container_lock_perm): Tracked<&LockPerm>,
    Tracked(parent_lock_perm): Tracked<&LockPerm>,
    Tracked(staging_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_lock_perm): Tracked<&LockPerm>,
) -> (ret: (RwLockProcessPtr, RwLockPageTableRoot, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        index_valid(NUM_PAGES, page_ptr2page_index(process_page_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(pagetable_page_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(l4_page_ptr)),
        !old(krnl).prc_mp.dom().contains(process_page_ptr),
        !old(krnl).pt_mp.dom().contains(pagetable_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).wlocked_by(old(lctx)),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        old(krnl).prc_mp.spec_index(parent_ptr).wlocked_by(old(lctx)),
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        parent_lock_perm.state() is WriteLock,
        parent_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(staging_thread_ptr),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(staging_thread_ptr).wlocked_by(old(lctx)),
        !old(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 3,
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr],
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        staging_thread_lock_perm.state() is WriteLock,
        staging_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        staging_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).wlocked_by(old(lctx)),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        pcid_allocator_lock_perm.state() is WriteLock,
        pcid_allocator_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().wlocked_by(old(lctx)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().wlocked_by(old(lctx)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().wlocked_by(old(lctx)),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        kernel_u_create_process_changed(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), parent_ptr, process_page_ptr),
        kernel_k_to_kernel_u(*final(krnl)) != kernel_k_to_kernel_u(*old(krnl)),
        ret.0 == process_page_ptr,
        ret.1 == pagetable_page_ptr,
        final(krnl).prc_mp.dom() =~= old(krnl).prc_mp.dom().insert(process_page_ptr),
        final(krnl).pt_mp.dom() =~= old(krnl).pt_mp.dom().insert(pagetable_page_ptr),
        final(krnl).prc_mp.spec_index(process_page_ptr).wlocked_by(final(lctx)),
        final(krnl).pt_mp.spec_index(pagetable_page_ptr).wlocked_by(final(lctx)),
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).prc_mp.spec_index(process_page_ptr).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable_page_ptr).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.spec_index(process_page_ptr).view_rodata().view().owning_container == container_ptr,
        final(krnl).prc_mp.spec_index(process_page_ptr).view_rodata().view().parent == Some(parent_ptr),
        final(krnl).prc_mp.spec_index(process_page_ptr).view_rodata().view().depth == old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().depth + 1,
        final(krnl).prc_mp.spec_index(process_page_ptr).view().pagetable == pagetable_page_ptr,
        final(krnl).prc_mp.spec_index(process_page_ptr).view().pcid == pcid,
        final(krnl).prc_mp.spec_index(process_page_ptr).view().iommu_table is None,
        final(krnl).prc_mp.spec_index(process_page_ptr).view().quota_4k == 0,
        final(krnl).prc_mp.spec_index(process_page_ptr).view().quota_2m == 0,
        final(krnl).prc_mp.spec_index(process_page_ptr).view().quota_1g == 0,
        final(krnl).prc_mp.spec_index(process_page_ptr).view().owned_threads.view() == Seq::<RwLockThreadPtr>::empty(),
        !final(krnl).prc_mp.spec_index(process_page_ptr).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable_page_ptr).view().proc_ptr == process_page_ptr,
        final(krnl).pt_mp.spec_index(pagetable_page_ptr).view().pcid_value() == pcid,
        final(krnl).pt_mp.spec_index(pagetable_page_ptr).view().kernel_l4_end == old(krnl).dflt_pt.view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable_page_ptr).view().is_empty(),
        forall|pt: RwLockPageTableRoot| #![auto]
            old(krnl).pt_mp.dom().contains(pt) ==> final(krnl).pt_mp.spec_index(pt) == old(krnl).pt_mp.spec_index(pt),
        forall|pt: RwLockPageTableRoot|
            #![trigger old(krnl).pt_mp.lock_id_by_key(pt)]
            #![trigger final(krnl).pt_mp.lock_id_by_key(pt)]
            old(krnl).pt_mp.dom().contains(pt) ==> final(krnl).pt_mp.lock_id_by_key(pt) == old(krnl).pt_mp.lock_id_by_key(pt),
        forall|pt: RwLockPageTableRoot|
            #![trigger final(krnl).pt_mp.spec_index(pt).view().user_view()]
            old(krnl).pt_mp.dom().contains(pt) ==> final(krnl).pt_mp.spec_index(pt).view().user_view() == old(krnl).pt_mp.spec_index(pt).view().user_view(),
        final(krnl).prc_mp.spec_index(parent_ptr).view().children.view() == old(krnl).prc_mp.spec_index(parent_ptr).view().children.view().push(process_page_ptr),
        !final(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        process_add_child_ensures(old(krnl).ctn_mp.spec_index(container_ptr).view().root_process, old(krnl).ctn_mp.spec_index(container_ptr).view().owned_processes.view(), old(krnl).prc_mp, final(krnl).prc_mp, parent_ptr, process_page_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).view().owned_processes.view() =~= old(krnl).ctn_mp.spec_index(container_ptr).view().owned_processes.view().insert(process_page_ptr),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        !final(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().id_to_proc.view().spec_index(pcid as int) =~= old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().id_to_proc.view().spec_index(pcid as int).insert(process_page_ptr),
        final(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k - 3,
        final(krnl).thr_mp.dom().contains(staging_thread_ptr),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_proc,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_container,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().state == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        !final(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).wlocked_by(final(lctx)),
        staging_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.spec_index(container_ptr).wlocked_by(final(lctx)),
        container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.spec_index(parent_ptr).wlocked_by(final(lctx)),
        parent_lock_perm.lock_id() == final(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        final(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).wlocked_by(final(lctx)),
        pcid_allocator_lock_perm.lock_id() == final(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().wlocked_by(final(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().wlocked_by(final(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().wlocked_by(final(lctx)),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == final(lctx).thread_id(),
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == final(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == final(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().locking_thread()->Write_lock_id,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).sched_mp == old(krnl).sched_mp,
        final(krnl).ep_mp == old(krnl).ep_mp,
        final(krnl).it_mp == old(krnl).it_mp,
        final(krnl).irt == old(krnl).irt,
        final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
        final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
        final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
        final(krnl).dflt_pt == old(krnl).dflt_pt,
        container_objects_unlocked_except(old(krnl).ctn_mp, old(lctx).thread_id(), set![container_ptr]) ==> container_objects_unlocked_except(final(krnl).ctn_mp, final(lctx).thread_id(), set![container_ptr]),
        process_objects_unlocked_except(old(krnl).prc_mp, old(lctx).thread_id(), set![parent_ptr]) ==> process_objects_unlocked_except(final(krnl).prc_mp, final(lctx).thread_id(), set![parent_ptr, process_page_ptr]),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![staging_thread_ptr]) ==> thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![staging_thread_ptr]),
        page_objects_unlocked_except(old(krnl).pg_arr, old(lctx).thread_id(), set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr)]) ==> page_objects_unlocked_except(final(krnl).pg_arr, final(lctx).thread_id(), set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr)]),
        pagetable_objects_unlocked(old(krnl).pt_mp, old(lctx).thread_id()) ==> pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), set![pagetable_page_ptr]),
        forall|exceptions: Set<RwLockPageTableRoot>|
            #![trigger pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), exceptions)]
            !exceptions.contains(pagetable_page_ptr)
            && pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), exceptions)
            ==> pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), exceptions.insert(pagetable_page_ptr)),
        pcid_allocator_objects_unlocked_except(old(krnl).pcid_allc_mp, old(lctx).thread_id(), set![pcid_allocator_ptr]) ==> pcid_allocator_objects_unlocked_except(final(krnl).pcid_allc_mp, final(lctx).thread_id(), set![pcid_allocator_ptr]),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map().insert(process_page_ptr, TypedHeldLock { lock_id: final(krnl).prc_mp.lock_id_by_key(process_page_ptr), mode: TypedLockMode::Write }),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map().insert(pagetable_page_ptr, TypedHeldLock { lock_id: final(krnl).pt_mp.lock_id_by_key(pagetable_page_ptr), mode: TypedLockMode::Write }),
        final(lctx).page_lock_map() == old(lctx).page_lock_map()
            .insert(page_ptr2page_index(l4_page_ptr), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(l4_page_ptr)), mode: TypedLockMode::Write })
            .insert(page_ptr2page_index(pagetable_page_ptr), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pagetable_page_ptr)), mode: TypedLockMode::Write })
            .insert(page_ptr2page_index(process_page_ptr), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(process_page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
{
    let process_page_index = page_ptr2page_index(process_page_ptr);
    let pagetable_page_index = page_ptr2page_index(pagetable_page_ptr);
    let l4_page_index = page_ptr2page_index(l4_page_ptr);
    proof {
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        assert(krnl.pg_arr.inv()) by { reveal(KernelK::inv); reveal(KernelK::subsystems_inv); reveal(page_array_wf); };
        assert(krnl.pt_mp.perms_wf()) by { reveal(KernelK::inv); reveal(KernelK::subsystems_inv); reveal(pagetable_perms_wf); };
        assert(krnl.pg_arr.spec_index(l4_page_index).view().is_init() && krnl.pg_arr.spec_index(l4_page_index).view().view().inv() && krnl.pg_arr.spec_index(l4_page_index).view().view().addr == l4_page_ptr && krnl.pg_arr.spec_index(l4_page_index).view().view().perm_4k.view().is_some()) by { reveal(page_array_wf); };
        assert(krnl.pg_arr.spec_index(pagetable_page_index).view().is_init() && krnl.pg_arr.spec_index(pagetable_page_index).view().view().inv() && krnl.pg_arr.spec_index(pagetable_page_index).view().view().addr == pagetable_page_ptr && krnl.pg_arr.spec_index(pagetable_page_index).view().view().perm_4k.view().is_some()) by { reveal(page_array_wf); };
        assert(krnl.pg_arr.spec_index(process_page_index).view().is_init() && krnl.pg_arr.spec_index(process_page_index).view().view().inv() && krnl.pg_arr.spec_index(process_page_index).view().view().addr == process_page_ptr && krnl.pg_arr.spec_index(process_page_index).view().view().perm_4k.view().is_some()) by { reveal(page_array_wf); };
        assert(krnl.dflt_pt.view().wf()) by { reveal(KernelK::inv); reveal(KernelK::subsystems_inv); reveal(KernelK::default_pagetable_wf); };
        assert(pei_valid(krnl.dflt_pt.view().kernel_l4_end)) by { reveal(PageTable::kernel_entries_wf); };
    }
    let ghost old_l4_page_lock_id = krnl.pg_arr.lock_id_by_index(l4_page_index);
    let l4_page_mut = krnl.pg_arr.borrow_mut_typed(l4_page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(l4_page_lock_perm));
    let Tracked(l4_page_perm) = take_perm_4k(l4_page_mut);
    l4_page_mut.state = PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable_page_ptr } };
    proof { lctx.update_lock_id(KernelObjId::Page(l4_page_index), old_l4_page_lock_id, krnl.pg_arr.lock_id_by_index(l4_page_index)); }
    let (l4_ptr, Tracked(mut l4_perm)) = page_perm_to_page_map(l4_page_ptr, Tracked(l4_page_perm));
    let default_pt = krnl.dflt_pt.borrow();
    default_pt.copy_kernel_entries_to_unpublished_root(l4_ptr, Tracked(&mut l4_perm));
    proof { assert(default_pt.kernel_entries.view().len() == default_pt.kernel_l4_end) by { reveal(PageTable::kernel_entries_wf); }; }
    let pagetable_value = PageTable::<PT_TYPE>::new(Some(pcid), Ghost(default_pt.kernel_entries.view()), l4_ptr, Tracked(l4_perm), default_pt.kernel_l4_end, process_page_ptr);

    let ghost old_pagetable_page_lock_id = krnl.pg_arr.lock_id_by_index(pagetable_page_index);
    let pagetable_page_mut = krnl.pg_arr.borrow_mut_typed(pagetable_page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(pagetable_page_lock_perm));
    let Tracked(pagetable_page_perm) = take_perm_4k(pagetable_page_mut);
    pagetable_page_mut.state = PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot };
    proof { lctx.update_lock_id(KernelObjId::Page(pagetable_page_index), old_pagetable_page_lock_id, krnl.pg_arr.lock_id_by_index(pagetable_page_index)); }
    let Tracked(pagetable_lock_perm) = krnl.retype_page_to_pagetable_and_insert(pagetable_page_ptr, pagetable_value, Tracked(pagetable_page_perm), Tracked(&mut *lctx));

    let parent_depth = krnl.prc_mp.borrow_rodata(parent_ptr).borrow().depth;
    let cr3 = l4_ptr;
    let process_value = Process::new_fresh(process_page_ptr, pcid, pagetable_page_ptr, krnl.ctn_mp.borrow_rodata(container_ptr).borrow().depth, parent_depth + 1);
    let process_rodata = ReadOnlyNode::new(ProcessRO { owning_container: container_ptr, container_depth: krnl.ctn_mp.borrow_rodata(container_ptr).borrow().depth, parent: Some(parent_ptr), depth: parent_depth + 1, pagetable: pagetable_page_ptr, cr3, pcid }, Ghost(process_page_ptr));
    let process_ghost = ProcessGhost { uppertree_seq: Ghost(krnl.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr)), subtree_set: Ghost(Set::empty()) };
    let ghost old_process_page_lock_id = krnl.pg_arr.lock_id_by_index(process_page_index);
    let process_page_mut = krnl.pg_arr.borrow_mut_typed(process_page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(process_page_lock_perm));
    let Tracked(process_page_perm) = take_perm_4k(process_page_mut);
    process_page_mut.state = PageState::Allocated4k { state: Allocated4KPageState::AsProcess };
    proof { lctx.update_lock_id(KernelObjId::Page(process_page_index), old_process_page_lock_id, krnl.pg_arr.lock_id_by_index(process_page_index)); }
    let Tracked(process_lock_perm) = krnl.retype_page_to_process_and_insert(process_page_ptr, process_value, process_rodata, process_ghost, Tracked(process_page_perm), Tracked(&mut *lctx));

    let child_mut = krnl.prc_mp.borrow_mut_typed(process_page_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm));
    let (child_node_addr, mut child_node_perm) = child_mut.parent_linkedlist_node.take();
    node_update_value(child_node_addr, &mut child_node_perm, process_page_ptr);
    let parent_mut = krnl.prc_mp.borrow_mut_typed(parent_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(parent_lock_perm));
    parent_mut.children.push_tail(child_node_addr, child_node_perm);

    let ghost ancestors = krnl.prc_mp.spec_index(process_page_ptr).view_ghost().uppertree_seq.view();
    proof {
        assert(ancestors.to_set().subset_of(krnl.prc_mp.dom())) by { ancestors.to_set_ensures(); reveal(process_uppertree_seq_wf); };
        assert(!ancestors.to_set().contains(process_page_ptr)) by { ancestors.to_set_ensures(); reveal(process_tree_fields_wf); };
        process_insert_child_into_ancestor_subtree_sets(&mut krnl.prc_mp, ancestors, process_page_ptr);
    }
    let container_mut = krnl.ctn_mp.borrow_mut_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(container_lock_perm));
    container_mut.owned_processes = Ghost(container_mut.owned_processes.view().insert(process_page_ptr));
    let pcid_allocator_mut = krnl.pcid_allc_mp.borrow_mut_typed(pcid_allocator_ptr, Ghost(lctx.pcid_allocator_lock_map()), Tracked(&*lctx), Tracked(pcid_allocator_lock_perm));
    pcid_allocator_mut.alloc(pcid, process_page_ptr);
    let staging_thread_mut = krnl.thr_mp.borrow_mut_typed(staging_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    staging_thread_mut.temp_alloc_cache_4k = Ghost(staging_thread_mut.temp_alloc_cache_4k.view().remove(process_page_ptr).remove(pagetable_page_ptr).remove(l4_page_ptr));
    staging_thread_mut.quota_4k = staging_thread_mut.quota_4k - 3;

    proof {
        assert(process_add_child_ensures(old(krnl).ctn_mp.spec_index(container_ptr).view().root_process, old(krnl).ctn_mp.spec_index(container_ptr).view().owned_processes.view(), old(krnl).prc_mp, krnl.prc_mp, parent_ptr, process_page_ptr)) by { reveal(process_add_child_ensures); reveal(process_perms_wf); reveal(LinkedList::wf_value_list); seq_push_lemma::<RwLockProcessPtr>(); };
        process_add_child_preserves_tree_wf(old(krnl).ctn_mp.spec_index(container_ptr).view().root_process, old(krnl).ctn_mp.spec_index(container_ptr).view().owned_processes.view(), old(krnl).prc_mp, krnl.prc_mp, parent_ptr, process_page_ptr);
        assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(page_array_wf); reveal(pagetable_perms_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(pcid_allocator_perms_wf); reveal(LinkedList::wf_value_list); };
        assert(krnl.memory_management_inv()) by {
            reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf); reveal(container_page_owner_wf);
            reveal(hugepage_2m_wf); reveal(hugepage_1g_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
            reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(container_pages_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(thread_pages_wf); reveal(pcid_allocator_pages_wf);
            reveal(thread_staged_pages_4k_wf); reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_1g_wf); reveal(endpoint_pages_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match);
            reveal(allocator_free_page_ptrs_wf); reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf); reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf);
            reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf);
            reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf);
            reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf);
            lemma_process_effective_quota_4k_fold_sum_eq_forall(); lemma_process_effective_quota_2m_fold_sum_eq_forall(); lemma_process_effective_quota_1g_fold_sum_eq_forall();
        };
        assert(krnl.process_management_inv()) by {
            reveal(container_process_wf); reveal(per_container_process_tree_wf); reveal(container_endpoint_wf); reveal(container_cpu_wf); reveal(container_scheduler_wf); reveal(container_pcid_allocator_wf); reveal(process_pcid_allocator_wf);
            reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(thread_caller_callee_wf); reveal(container_thread_endpoint_wf); reveal(container_thread_scheduler_wf); reveal(container_thread_wf); reveal(process_cpu_wf); reveal(process_thread_wf); reveal(process_empty_thread_list_wlocked); reveal(thread_cpu_wf);
        };
        assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
        assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr)) by { reveal(tlb_wf_spec); };
        assert(iommu_root_table_process_wf(&krnl.irt, krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_root_table_process_wf); };
        assert(process_pci_function_ownership_wf(&krnl.irt, krnl.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
        assert(iommu_tlb_wf_spec(krnl.iommu_tlb, &krnl.irt, krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_tlb_wf_spec); };
        assert(krnl.inv()) by { reveal(KernelK::inv); };
    }
    (process_page_ptr, pagetable_page_ptr, Tracked(process_lock_perm), Tracked(pagetable_lock_perm))
}

}
