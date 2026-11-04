use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub fn create_process_with_iommu_from_staged_pages(
    krnl: &mut KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr,
    pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(process_page_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<&LockPerm>, Tracked(iommu_table_page_lock_perm): Tracked<&LockPerm>,
    Tracked(iommu_l4_page_lock_perm): Tracked<&LockPerm>, Tracked(parent_lock_perm): Tracked<&LockPerm>,
    Tracked(staging_thread_lock_perm): Tracked<&LockPerm>, Tracked(pcid_allocator_lock_perm): Tracked<&LockPerm>,
) -> (ret: (RwLockProcessPtr, RwLockPageTableRoot, RwLockPageTableRoot, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        page_ptr_valid(iommu_table_pg_ptr),
        page_ptr_valid(iommu_l4_pg_ptr),
        index_valid(NUM_PAGES, page_ptr2page_index(process_pg_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(pagetable_pg_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(l4_pg_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(iommu_table_pg_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(iommu_l4_pg_ptr)),
        !old(krnl).prc_mp.dom().contains(process_pg_ptr),
        !old(krnl).pt_mp.dom().contains(pagetable_pg_ptr),
        !old(krnl).it_mp.dom().contains(iommu_table_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        process_pg_ptr != iommu_table_pg_ptr,
        process_pg_ptr != iommu_l4_pg_ptr,
        pagetable_pg_ptr != iommu_table_pg_ptr,
        pagetable_pg_ptr != iommu_l4_pg_ptr,
        l4_pg_ptr != iommu_table_pg_ptr,
        l4_pg_ptr != iommu_l4_pg_ptr,
        iommu_table_pg_ptr != iommu_l4_pg_ptr,
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == ctn_ptr,
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        parent_lock_perm.state() is WriteLock,
        parent_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.dom().contains(staging_thrd_ptr),
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().owning_container == ctn_ptr,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), staging_thrd_ptr, TypedLockMode::Write),
        !old(krnl).thrd_mp.spec_index(staging_thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k >= 5,
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view() =~= set![process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, iommu_table_pg_ptr, iommu_l4_pg_ptr],
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().free_quota_pending_clean(),
        staging_thread_lock_perm.state() is WriteLock,
        staging_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        staging_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allc_ptr),
        old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator == pcid_allc_ptr,
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allc_ptr, TypedLockMode::Write),
        old(krnl).pcid_allc_mp.spec_index(pcid_allc_ptr).view().pcid_is_free(pcid),
        pcid_allocator_lock_perm.state() is WriteLock,
        pcid_allocator_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allc_ptr).locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().owning_container == ctn_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_pg_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().owning_container == ctn_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_pg_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_pg_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_pg_ptr)).view().view().owning_container == ctn_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(iommu_table_pg_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(iommu_l4_pg_ptr), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().locking_thread()->Write_lock_id,
        iommu_table_page_lock_perm.state() is WriteLock,
        iommu_table_page_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_pg_ptr)).view().locking_thread()->Write_lock_id,
        iommu_l4_page_lock_perm.state() is WriteLock,
        iommu_l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_pg_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr, prc_mp: final(krnl).prc_mp, pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, it_mp: final(krnl).it_mp,
            ctn_mp: final(krnl).ctn_mp, thrd_mp: final(krnl).thrd_mp, pcid_allc_mp: final(krnl).pcid_allc_mp, ..*old(krnl)
        }),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom().insert(process_pg_ptr),
        final(krnl).prc_mp.spec_index(parent_ptr).view().owned_threads == old(krnl).prc_mp.spec_index(parent_ptr).view().owned_threads,
        final(krnl).prc_mp.spec_index(parent_ptr).being_killed() == old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        !final(krnl).prc_mp.spec_index(process_pg_ptr).being_killed(),
        !final(krnl).prc_mp.spec_index(process_pg_ptr).view().zombie,
        final(krnl).prc_mp.spec_index(process_pg_ptr).view().state.view() is Creating,
        final(krnl).prc_mp.spec_index(process_pg_ptr).view_rodata().view().owning_container == ctn_ptr,
        final(krnl).prc_mp.spec_index(process_pg_ptr).view_rodata().view().pagetable == pagetable_pg_ptr,
        final(krnl).prc_mp.spec_index(process_pg_ptr).view().iommu_table == Some(iommu_table_pg_ptr),
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom().insert(pagetable_pg_ptr),
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
            old(krnl).pt_mp.dom().contains(pt) ==> final(krnl).pt_mp.spec_index(pt) == old(krnl).pt_mp.spec_index(pt),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_pg_ptr).is_empty(),
        final(krnl).pt_mp.spec_index(pagetable_pg_ptr).view().proc_ptr == process_pg_ptr,
        final(krnl).prc_mp.spec_index(process_pg_ptr).view().pagetable == pagetable_pg_ptr,
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        final(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(ctn_ptr).control() == old(krnl).ctn_mp.spec_index(ctn_ptr).control(),
        final(krnl).thrd_mp.dom() == old(krnl).thrd_mp.dom(),
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view() == (Thread {
            quota_4k: (old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k - 5) as usize,
            temp_alloc_cache_4k: Ghost(Set::empty()), ..old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view()
        }),
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).being_killed(),
        final(krnl).pcid_allc_mp.dom() == old(krnl).pcid_allc_mp.dom(),
        final(krnl).it_mp.dom() == old(krnl).it_mp.dom().insert(iommu_table_pg_ptr),
        final(krnl).it_mp.spec_index(iommu_table_pg_ptr).view().is_empty(),
        final(krnl).it_mp.spec_index(iommu_table_pg_ptr).view().did is None,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        ret.0 == process_pg_ptr,
        ret.1 == pagetable_pg_ptr,
        ret.2 == iommu_table_pg_ptr,
        create_process_from_staged_pages_eof_transition_framing(*old(krnl), *final(krnl), process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, true, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_pg_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_pg_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).iommu_table_lock_map(), iommu_table_pg_ptr, TypedLockMode::Write),
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).prc_mp.spec_index(process_pg_ptr).locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable_pg_ptr).locking_thread()->Write_lock_id,
        ret.5.view().state() is WriteLock,
        ret.5.view().thread_id() == final(lctx).thread_id(),
        ret.5.view().lock_id() == final(krnl).it_mp.spec_index(iommu_table_pg_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), staging_thrd_ptr, TypedLockMode::Write),
        staging_thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(staging_thrd_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        parent_lock_perm.lock_id() == final(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allc_ptr, TypedLockMode::Write),
        pcid_allocator_lock_perm.lock_id() == final(krnl).pcid_allc_mp.spec_index(pcid_allc_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(process_pg_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pagetable_pg_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(l4_pg_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(iommu_table_pg_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(iommu_l4_pg_ptr), TypedLockMode::Write),
        process_page_lock_perm.thread_id() == final(lctx).thread_id(),
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.thread_id() == final(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.thread_id() == final(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().locking_thread()->Write_lock_id,
        iommu_table_page_lock_perm.thread_id() == final(lctx).thread_id(),
        iommu_table_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_pg_ptr)).view().locking_thread()->Write_lock_id,
        iommu_l4_page_lock_perm.thread_id() == final(lctx).thread_id(),
        iommu_l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_pg_ptr)).view().locking_thread()->Write_lock_id,
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).process_lock_map() == old(lctx).process_lock_map().insert(process_pg_ptr, TypedHeldLock { lock_id: final(krnl).prc_mp.lock_id_by_key(process_pg_ptr), mode: TypedLockMode::Write }),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map().insert(pagetable_pg_ptr, TypedHeldLock { lock_id: final(krnl).pt_mp.lock_id_by_key(pagetable_pg_ptr), mode: TypedLockMode::Write }),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map().insert(iommu_table_pg_ptr, TypedHeldLock { lock_id: final(krnl).it_mp.lock_id_by_key(iommu_table_pg_ptr), mode: TypedLockMode::Write }),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().insert(page_ptr2page_index(l4_pg_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(l4_pg_ptr)), mode: TypedLockMode::Write,
            }).insert(page_ptr2page_index(pagetable_pg_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pagetable_pg_ptr)), mode: TypedLockMode::Write,
            }).insert(page_ptr2page_index(iommu_l4_pg_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(iommu_l4_pg_ptr)), mode: TypedLockMode::Write,
            }).insert(page_ptr2page_index(iommu_table_pg_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(iommu_table_pg_ptr)), mode: TypedLockMode::Write,
            }).insert(page_ptr2page_index(process_pg_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(process_pg_ptr)), mode: TypedLockMode::Write,
            }),
        final(krnl).prc_mp.lock_id_by_key(process_pg_ptr).major == PROCESS_LOCK_MAJOR,
        final(krnl).pt_mp.lock_id_by_key(pagetable_pg_ptr).major == PAGE_TABLE_LOCK_MAJOR,
        final(krnl).it_mp.lock_id_by_key(iommu_table_pg_ptr).major == IOMMU_TABLE_LOCK_MAJOR,
{
    let process_pg_idx = page_ptr2page_index(process_pg_ptr);
    let pagetable_pg_idx = page_ptr2page_index(pagetable_pg_ptr);
    let l4_pg_idx = page_ptr2page_index(l4_pg_ptr);
    let iommu_table_pg_idx = page_ptr2page_index(iommu_table_pg_ptr);
    let iommu_l4_pg_idx = page_ptr2page_index(iommu_l4_pg_ptr);
    proof {
        assert({
            &&& process_pg_ptr == page_index2page_ptr(process_pg_idx)
            &&& pagetable_pg_ptr == page_index2page_ptr(pagetable_pg_idx)
            &&& l4_pg_ptr == page_index2page_ptr(l4_pg_idx)
            &&& iommu_table_pg_ptr == page_index2page_ptr(iommu_table_pg_idx)
            &&& iommu_l4_pg_ptr == page_index2page_ptr(iommu_l4_pg_idx)
        }) by { page_ptr_roundtrip(); };
        assert(krnl.pt_mp.perms_wf()) by { pagetable_perms_wf_map(krnl.pt_mp); };
        assert(krnl.it_mp.perms_wf()) by { iommu_table_perms_wf_map(krnl.it_mp); };
        assert(krnl.prc_mp.perms_wf() && krnl.prc_mp.view().spec_index(parent_ptr).is_init() && krnl.prc_mp.view().spec_index(parent_ptr).addr() == parent_ptr && krnl.prc_mp.spec_index(parent_ptr).inv()
            && krnl.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().no_duplicates() && krnl.prc_mp.spec_index(parent_ptr).view().children.view().no_duplicates()
            && krnl.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().len() == krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().depth) by {
            process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, parent_ptr);
        };
        assert(krnl.ctn_mp.perms_wf() && krnl.ctn_mp.view().spec_index(ctn_ptr).is_init() && krnl.ctn_mp.view().spec_index(ctn_ptr).addr() == ctn_ptr && krnl.ctn_mp.spec_index(ctn_ptr).inv()) by {
            container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, ctn_ptr);
        };
        assert(krnl.pcid_allc_mp.perms_wf() && krnl.pcid_allc_mp.spec_index(pcid_allc_ptr).inv()) by { pcid_allocator_perms_wf_map(krnl.pcid_allc_mp); pcid_allocator_perms_wf_at(krnl.pcid_allc_mp, pcid_allc_ptr); };
        assert(krnl.thrd_mp.perms_wf() && krnl.thrd_mp.spec_index(staging_thrd_ptr).is_init() && krnl.thrd_mp.spec_index(staging_thrd_ptr).inv()) by { thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, staging_thrd_ptr); };
        assert(krnl.pg_arr.spec_index(l4_pg_idx).view().is_init() && krnl.pg_arr.spec_index(l4_pg_idx).view().view().inv() && krnl.pg_arr.spec_index(l4_pg_idx).view().view().addr == l4_pg_ptr && krnl.pg_arr.spec_index(l4_pg_idx).view().view().perm_4k.view().is_some()
        ) by { page_array_wf_at(krnl.pg_arr, l4_pg_idx); };
        assert(krnl.pg_arr.spec_index(pagetable_pg_idx).view().is_init() && krnl.pg_arr.spec_index(pagetable_pg_idx).view().view().inv()
            && krnl.pg_arr.spec_index(pagetable_pg_idx).view().view().addr == pagetable_pg_ptr && krnl.pg_arr.spec_index(pagetable_pg_idx).view().view().perm_4k.view().is_some()
        ) by { page_array_wf_at(krnl.pg_arr, pagetable_pg_idx); };
        assert(krnl.pg_arr.spec_index(process_pg_idx).view().is_init() && krnl.pg_arr.spec_index(process_pg_idx).view().view().inv()
            && krnl.pg_arr.spec_index(process_pg_idx).view().view().addr == process_pg_ptr && krnl.pg_arr.spec_index(process_pg_idx).view().view().perm_4k.view().is_some()
        ) by { page_array_wf_at(krnl.pg_arr, process_pg_idx); };
        assert(krnl.pg_arr.spec_index(iommu_table_pg_idx).view().is_init() && krnl.pg_arr.spec_index(iommu_table_pg_idx).view().view().inv()
            && krnl.pg_arr.spec_index(iommu_table_pg_idx).view().view().addr == iommu_table_pg_ptr && krnl.pg_arr.spec_index(iommu_table_pg_idx).view().view().perm_4k.view().is_some()
        ) by { page_array_wf_at(krnl.pg_arr, iommu_table_pg_idx); };
        assert(krnl.pg_arr.spec_index(iommu_l4_pg_idx).view().is_init() && krnl.pg_arr.spec_index(iommu_l4_pg_idx).view().view().inv()
            && krnl.pg_arr.spec_index(iommu_l4_pg_idx).view().view().addr == iommu_l4_pg_ptr && krnl.pg_arr.spec_index(iommu_l4_pg_idx).view().view().perm_4k.view().is_some()
        ) by { page_array_wf_at(krnl.pg_arr, iommu_l4_pg_idx); };
        assert(krnl.dflt_pt.view().wf()) by { krnl.default_pagetable_wf_implies_view_inv(); };
        assert(pei_valid(krnl.dflt_pt.view().kernel_l4_end) && krnl.dflt_pt.view().kernel_entries.view().len() == krnl.dflt_pt.view().kernel_l4_end) by { krnl.dflt_pt.view().kernel_entries_wf_len_at(); };
    }
    let ghost parent_ancestors = krnl.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
    let ghost ancestors = parent_ancestors.push(parent_ptr);
    let ghost parent_children = krnl.prc_mp.spec_index(parent_ptr).view().children.view();
    proof {
        let process_tree_dom = krnl.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view();
        let root_process = krnl.ctn_mp.spec_index(ctn_ptr).view().root_process;
        assert(process_tree_dom.contains(parent_ptr)) by { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, parent_ptr); };
        assert(process_tree_wf(root_process, process_tree_dom, krnl.prc_mp)) by { per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, ctn_ptr); };
        assert(process_tree_dom.subset_of(krnl.prc_mp.dom())) by { container_process_wf_container_at(krnl.ctn_mp, krnl.prc_mp, ctn_ptr, parent_ptr); };
        assert(parent_ancestors.to_set().subset_of(process_tree_dom)) by { parent_ancestors.to_set_ensures(); process_uppertree_seq_wf_implies_ancestors_in_dom(root_process, process_tree_dom, krnl.prc_mp, parent_ptr); };
        assert(!parent_ancestors.contains(parent_ptr)) by { process_uppertree_seq_wf_at(root_process, process_tree_dom, krnl.prc_mp, parent_ptr, parent_ptr); };
        assert(!krnl.prc_mp.spec_index(parent_ptr).view().children.view().contains(process_pg_ptr)) by { process_children_parent_wf_at(root_process, process_tree_dom, krnl.prc_mp, parent_ptr, process_pg_ptr); };
        assert(parent_children.len() <= NUM_PAGES) by { process_children_parent_wf_implies_children_in_tree(root_process, process_tree_dom, krnl.prc_mp, parent_ptr); lemma_kernel_object_ptr_seq_len_bounded(&*krnl, parent_children); };
        assert(krnl.pcid_allc_mp.spec_index(pcid_allc_ptr).view().process_is_unallocated(process_pg_ptr)) by { process_pcid_allocator_wf_unallocated_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, pcid_allc_ptr, process_pg_ptr); };
    }
    let ghost page_locks = lctx.page_lock_map();
    let Tracked(l4_page_perm) = page_array_retype_owned_4k(&mut krnl.pg_arr, l4_pg_idx, PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable_pg_ptr, table_type: PT_TYPE } }, Ghost(page_locks), Tracked(&*lctx), Tracked(l4_page_lock_perm));
    let ghost l4_page_locks = page_locks.insert(l4_pg_idx, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(l4_pg_idx), mode: TypedLockMode::Write });
    let (l4_ptr, Tracked(mut l4_perm)) = page_perm_to_page_map(l4_pg_ptr, Tracked(l4_page_perm));
    let default_pt = krnl.dflt_pt.borrow();
    default_pt.copy_kernel_entries_to_unpublished_root(l4_ptr, Tracked(&mut l4_perm));
    let pagetable_higher = PageTableHigher::<PT_TYPE>::new(Some(pcid), Ghost(default_pt.kernel_entries.view()), l4_ptr, Tracked(l4_perm), default_pt.kernel_l4_end, process_pg_ptr);
    let tracked pagetable_lower = PageTableLower::<PT_TYPE>::tracked_empty(pagetable_higher);

    let Tracked(pagetable_page_perm) = page_array_retype_owned_4k(&mut krnl.pg_arr, pagetable_pg_idx, PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } }, Ghost(l4_page_locks), Tracked(&*lctx), Tracked(pagetable_page_lock_perm));
    let ghost pagetable_page_locks = l4_page_locks.insert(pagetable_pg_idx, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pagetable_pg_idx), mode: TypedLockMode::Write });
    let Tracked(pagetable_lock_perm) = krnl.retype_page_to_pagetable_and_insert(pagetable_pg_ptr, pagetable_higher, Tracked(pagetable_lower), Tracked(pagetable_page_perm), Tracked(&mut *lctx));

    let Tracked(iommu_l4_page_perm) = page_array_retype_owned_4k(
        &mut krnl.pg_arr, iommu_l4_pg_idx, PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: iommu_table_pg_ptr, table_type: IOMMU_TYPE } },
        Ghost(pagetable_page_locks), Tracked(&*lctx), Tracked(iommu_l4_page_lock_perm),
    );
    let ghost iommu_l4_page_locks = pagetable_page_locks.insert(iommu_l4_pg_idx, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(iommu_l4_pg_idx), mode: TypedLockMode::Write });
    let (iommu_l4_ptr, Tracked(iommu_l4_perm)) = page_perm_to_page_map(iommu_l4_pg_ptr, Tracked(iommu_l4_page_perm));
    let iommu_table_value = PageTable::<IOMMU_TYPE>::new(None, Ghost(Seq::empty()), iommu_l4_ptr, Tracked(iommu_l4_perm), 0, process_pg_ptr);

    let Tracked(iommu_table_page_perm) = page_array_retype_owned_4k(
        &mut krnl.pg_arr, iommu_table_pg_idx, PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } },
        Ghost(iommu_l4_page_locks), Tracked(&*lctx), Tracked(iommu_table_page_lock_perm),
    );
    let ghost iommu_table_page_locks = iommu_l4_page_locks.insert(iommu_table_pg_idx, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(iommu_table_pg_idx), mode: TypedLockMode::Write });
    let Tracked(iommu_table_lock_perm) = krnl.retype_page_to_iommu_table_and_insert(iommu_table_pg_ptr, iommu_table_value, Tracked(iommu_table_page_perm), Tracked(&mut *lctx));

    let parent_depth = krnl.prc_mp.borrow_rodata(parent_ptr).borrow().depth;
    let cr3 = l4_ptr;
    let mut process_value = Process::new_fresh(process_pg_ptr, pcid, pagetable_pg_ptr, krnl.ctn_mp.borrow_rodata(ctn_ptr).borrow().depth, parent_depth + 1);
    process_value.iommu_table = Some(iommu_table_pg_ptr);
    let process_rodata = ReadOnlyNode::new(ProcessRO {
        owning_container: ctn_ptr, container_depth: krnl.ctn_mp.borrow_rodata(ctn_ptr).borrow().depth, parent: Some(parent_ptr), depth: parent_depth + 1,
        pagetable: pagetable_pg_ptr, cr3, iommu_cr3: Some(iommu_l4_pg_ptr), iommu_table_ptr: Some(iommu_table_pg_ptr), pcid,
    }, Ghost(process_pg_ptr));
    let process_ghost = ProcessGhost { uppertree_seq: Ghost(ancestors), subtree_set: Ghost(Set::empty()), owned_pci_functions: Ghost(Set::empty()) };
    let Tracked(process_page_perm) = page_array_retype_owned_4k(&mut krnl.pg_arr, process_pg_idx, PageState::Allocated4k { state: Allocated4KPageState::AsProcess }, Ghost(iommu_table_page_locks), Tracked(&*lctx), Tracked(process_page_lock_perm));
    let Tracked(process_lock_perm) = krnl.retype_page_to_process_and_insert(process_pg_ptr, process_value, process_rodata, process_ghost, Tracked(process_page_perm), Tracked(&mut *lctx));

    process_map_link_new_child(&mut krnl.prc_mp, parent_ptr, process_pg_ptr, Ghost(ancestors), Tracked(&*lctx), Tracked(parent_lock_perm), Tracked(&process_lock_perm));
    proof { container_map_add_owned_process(&mut krnl.ctn_mp, ctn_ptr, process_pg_ptr, lctx.container_lock_map(), lctx.thread_id()); }
    pcid_allocator_map_alloc(&mut krnl.pcid_allc_mp, pcid_allc_ptr, process_pg_ptr, pcid, Tracked(&*lctx), Tracked(pcid_allocator_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thrd_mp, staging_thrd_ptr, process_pg_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thrd_mp, staging_thrd_ptr, pagetable_pg_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thrd_mp, staging_thrd_ptr, l4_pg_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thrd_mp, staging_thrd_ptr, iommu_table_pg_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thrd_mp, staging_thrd_ptr, iommu_l4_pg_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Page(l4_pg_idx), page_locks.index(l4_pg_idx).lock_id, krnl.pg_arr.lock_id_by_index(l4_pg_idx));
        lctx.update_lock_id(KernelObjId::Page(pagetable_pg_idx), page_locks.index(pagetable_pg_idx).lock_id, krnl.pg_arr.lock_id_by_index(pagetable_pg_idx));
        lctx.update_lock_id(KernelObjId::Page(iommu_l4_pg_idx), page_locks.index(iommu_l4_pg_idx).lock_id, krnl.pg_arr.lock_id_by_index(iommu_l4_pg_idx));
        lctx.update_lock_id(KernelObjId::Page(iommu_table_pg_idx), page_locks.index(iommu_table_pg_idx).lock_id, krnl.pg_arr.lock_id_by_index(iommu_table_pg_idx));
        lctx.update_lock_id(KernelObjId::Page(process_pg_idx), page_locks.index(process_pg_idx).lock_id, krnl.pg_arr.lock_id_by_index(process_pg_idx));
    }

    proof {
        krnl.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), iommu_table_pg_ptr);
        assert(create_process_from_staged_pages_eof_transition_framing(
            *old(krnl), *krnl, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, true, iommu_table_pg_ptr, iommu_l4_pg_ptr,
            parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid,
        )) by { reveal(create_process_from_staged_pages_eof_transition_framing); ancestors.to_set_ensures(); };
    }
    proof {
        create_process_with_iommu_from_staged_pages_eof_inv(
            *old(krnl), *krnl, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, iommu_table_pg_ptr, iommu_l4_pg_ptr,
            parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid,
        );
    }
    (process_pg_ptr, pagetable_pg_ptr, iommu_table_pg_ptr, Tracked(process_lock_perm), Tracked(pagetable_lock_perm), Tracked(iommu_table_lock_perm))
}
}
