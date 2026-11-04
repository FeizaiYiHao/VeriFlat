use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::opaque]
pub open spec fn new_container_bootstrap_4k_pages(
    allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr, cpu_set_page: PagePtr,
    process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr
) -> Set<PagePtr> {
    seq![allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page].to_set()
}

#[verifier::opaque]
pub open spec fn new_container_moved_pages(
    container_page: PagePtr, pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr
) -> Set<PagePtr> {
    page_2m_all_ptrs(page_ptr2page_index(container_page)).union(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))).union(new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page))
}

pub(super) fn publish_staged_container_root_mutation(
    krnl: &mut KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_page_count: usize, funding_page_head: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>, allocator_quota_4k: usize,
    process_quota_4k: usize, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(parent_container_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(container_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_4k_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_2m_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_1g_page_lock_perm): Tracked<&LockPerm>,
    Tracked(scheduler_page_lock_perm): Tracked<&LockPerm>, Tracked(cpu_set_page_lock_perm): Tracked<&LockPerm>,
    Tracked(process_page_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<&LockPerm>, Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        publish_staged_container_root_eof_preconditions(
            *old(krnl), parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_ctn_ptr, TypedLockMode::Write),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_ctn_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.spec_index(parent_ctn_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
        !old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_container == parent_ctn_ptr,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
        funding_page_count <= old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_4k - 8,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().free_quota_pending_clean(),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).len() == 8,
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(thread_page),
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        process_quota_4k <= funding_page_count,
        allocator_quota_4k == funding_page_count - process_quota_4k,
        !funding_pages.to_set().contains(thread_page),
        funding_pages.to_set().disjoint(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page)),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        forall|pg_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(pg_ptr)]
            funding_page_lock_perms.dom().contains(pg_ptr) ==> {
                &&& page_ptr_valid(pg_ptr)
                &&& funding_page_lock_perms.spec_index(pg_ptr).state() is WriteLock
                &&& funding_page_lock_perms.spec_index(pg_ptr).thread_id() == old(lctx).thread_id()
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr })
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr),).view().view().owning_container == parent_ctn_ptr
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(pg_ptr).lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr),).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(pcid_allocator_page),),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_4k_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_2m_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_1g_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        scheduler_page_lock_perm.state() is WriteLock,
        cpu_set_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_page_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).pt_mp.perms_wf(),
        final(krnl).pt_mp.spec_index(pagetable_page).inv(),
        final(krnl).ctn_mp.perms_wf(),
        final(krnl).ctn_mp.spec_index(parent_ctn_ptr).inv(),
        final(krnl).ctn_mp.spec_index(container_page).inv(),
        final(krnl).prc_mp.perms_wf(),
        final(krnl).prc_mp.spec_index(process_page).inv(),
        final(krnl).thrd_mp.perms_wf(),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).inv(),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost(),
        final(krnl).sched_mp.perms_wf(),
        final(krnl).sched_mp.spec_index(scheduler_page).inv(),
        final(krnl).cpu_set_mp.perms_wf(),
        final(krnl).cpu_set_mp.spec_index(cpu_set_page).inv(),
        final(krnl).pcid_allc_mp.perms_wf(),
        final(krnl).pcid_allc_mp.spec_index(pcid_allocator_page).inv(),
        final(krnl).allc_4k_mp.perms_wf(),
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).inv(),
        final(krnl).allc_2m_mp.perms_wf(),
        final(krnl).allc_2m_mp.spec_index(allocator_2m_page).inv(),
        final(krnl).allc_1g_mp.perms_wf(),
        final(krnl).allc_1g_mp.spec_index(allocator_1g_page).inv(),
        publish_staged_container_root_eof_transition_framing(
            *old(krnl), *final(krnl), parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
            allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
            funding_pages, allocator_quota_4k, process_quota_4k,
        ),
        final(lctx).page_lock_map().get(page_ptr2page_index(thread_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(thread_page)),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map().dom() == old(lctx).container_lock_map().dom().insert(container_page),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(lctx).container_lock_map().get(ptr)]
            #![trigger final(lctx).container_lock_map().spec_index(ptr)]
            #![trigger old(lctx).container_lock_map().get(ptr)]
            #![trigger old(lctx).container_lock_map().spec_index(ptr)]
            old(lctx).container_lock_map().dom().contains(ptr) && ptr != container_page ==> final(lctx).container_lock_map().get(ptr) == old(lctx).container_lock_map().get(ptr),
        final(lctx).process_lock_map().dom() == old(lctx).process_lock_map().dom().insert(process_page),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(lctx).process_lock_map().get(ptr)]
            #![trigger final(lctx).process_lock_map().spec_index(ptr)]
            #![trigger old(lctx).process_lock_map().get(ptr)]
            #![trigger old(lctx).process_lock_map().spec_index(ptr)]
            old(lctx).process_lock_map().dom().contains(ptr) && ptr != process_page ==> final(lctx).process_lock_map().get(ptr) == old(lctx).process_lock_map().get(ptr),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().insert(pcid_allocator_page),
        final(lctx).cpu_set_lock_map().dom() == old(lctx).cpu_set_lock_map().dom().insert(cpu_set_page),
        forall|ptr: RwLockCpuSetPtr|
            #![trigger final(lctx).cpu_set_lock_map().get(ptr)]
            #![trigger final(lctx).cpu_set_lock_map().spec_index(ptr)]
            #![trigger old(lctx).cpu_set_lock_map().get(ptr)]
            #![trigger old(lctx).cpu_set_lock_map().spec_index(ptr)]
            old(lctx).cpu_set_lock_map().dom().contains(ptr) && ptr != cpu_set_page ==> final(lctx).cpu_set_lock_map().get(ptr) == old(lctx).cpu_set_lock_map().get(ptr),
        final(lctx).pagetable_lock_map().dom() == old(lctx).pagetable_lock_map().dom().insert(pagetable_page),
        forall|ptr: RwLockPageTableRoot|
            #![trigger final(lctx).pagetable_lock_map().get(ptr)]
            #![trigger final(lctx).pagetable_lock_map().spec_index(ptr)]
            #![trigger old(lctx).pagetable_lock_map().get(ptr)]
            #![trigger old(lctx).pagetable_lock_map().spec_index(ptr)]
            old(lctx).pagetable_lock_map().dom().contains(ptr) && ptr != pagetable_page ==> final(lctx).pagetable_lock_map().get(ptr) == old(lctx).pagetable_lock_map().get(ptr),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allocator_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), cpu_set_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        container_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        scheduler_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(process_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().locking_thread()->Write_lock_id,
        forall|pg_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(pg_ptr)]
            funding_page_lock_perms.dom().contains(pg_ptr) ==> {
                &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(pg_ptr).lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), page_ptr2page_index(pcid_allocator_page),),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).ctn_mp.spec_index(container_page).locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).prc_mp.spec_index(process_page).locking_thread()->Write_lock_id,
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable_page).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).pcid_allc_mp.spec_index(pcid_allocator_page).locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).cpu_set_mp.spec_index(cpu_set_page).locking_thread()->Write_lock_id,
{
    hide(Seq::contains);
    let ghost pre_krnl = *krnl;
    let child_ctn_ptr = container_page;
    let child_pcid_allc_ptr = pcid_allocator_page;
    let child_allocator_4k_ptr = allocator_4k_page;
    let child_allocator_2m_ptr = allocator_2m_page;
    let child_allocator_1g_ptr = allocator_1g_page;
    let child_sched_ptr = scheduler_page;
    let child_cpu_set_ptr = cpu_set_page;
    let child_prc_ptr = process_page;
    let child_pagetable_ptr = pagetable_page;
    let root_pcid: Pcid = KERNEL_DEFAULT_PCID + 1usize;
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    let allocator_4k_index = page_ptr2page_index(allocator_4k_page);
    let allocator_2m_index = page_ptr2page_index(allocator_2m_page);
    let allocator_1g_index = page_ptr2page_index(allocator_1g_page);
    let scheduler_index = page_ptr2page_index(scheduler_page);
    let cpu_set_index = page_ptr2page_index(cpu_set_page);
    let process_index = page_ptr2page_index(process_page);
    let pagetable_index = page_ptr2page_index(pagetable_page);
    let l4_index = page_ptr2page_index(l4_page);
    let ghost bootstrap_pages = new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page);
    let ghost bootstrap_seq = seq![allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page];
    let ghost funding_indices = funding_pages.map_values(|pg_ptr: PagePtr| page_ptr2page_index(pg_ptr)).to_set();
    proof {
        assert({
            &&& old(krnl).ctn_mp.dom().contains(parent_ctn_ptr)
            &&& old(krnl).thrd_mp.dom().contains(current_thrd_ptr)
            &&& old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_4k >= 8
            &&& old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_2m >= 2
            &&& !old(krnl).ctn_mp.dom().contains(container_page)
            &&& !old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page)
            &&& !old(krnl).allc_4k_mp.dom().contains(allocator_4k_page)
            &&& !old(krnl).allc_2m_mp.dom().contains(allocator_2m_page)
            &&& !old(krnl).allc_1g_mp.dom().contains(allocator_1g_page)
            &&& !old(krnl).sched_mp.dom().contains(scheduler_page)
            &&& !old(krnl).cpu_set_mp.dom().contains(cpu_set_page)
            &&& !old(krnl).prc_mp.dom().contains(process_page)
            &&& !old(krnl).pt_mp.dom().contains(pagetable_page)
            &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thrd_ptr })
            &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thrd_ptr })
            &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr })
        }) by { reveal(publish_staged_container_root_eof_preconditions); };
        assert(bootstrap_seq.to_set() == bootstrap_pages) by { reveal(new_container_bootstrap_4k_pages); };
        bootstrap_seq.lemma_no_dup_set_cardinality(); page_ptr_seq_indices_no_duplicates(bootstrap_seq);
        assert({
            &&& allocator_2m_index != allocator_4k_index
            &&& allocator_1g_index != allocator_4k_index
            &&& allocator_1g_index != allocator_2m_index
            &&& scheduler_index != allocator_4k_index
            &&& scheduler_index != allocator_2m_index
            &&& scheduler_index != allocator_1g_index
            &&& cpu_set_index != allocator_4k_index
            &&& cpu_set_index != allocator_2m_index
            &&& cpu_set_index != allocator_1g_index
            &&& cpu_set_index != scheduler_index
            &&& process_index != allocator_4k_index
            &&& process_index != allocator_2m_index
            &&& process_index != allocator_1g_index
            &&& process_index != scheduler_index
            &&& process_index != cpu_set_index
            &&& pagetable_index != allocator_4k_index
            &&& pagetable_index != allocator_2m_index
            &&& pagetable_index != allocator_1g_index
            &&& pagetable_index != scheduler_index
            &&& pagetable_index != cpu_set_index
            &&& pagetable_index != process_index
            &&& l4_index != allocator_4k_index
            &&& l4_index != allocator_2m_index
            &&& l4_index != allocator_1g_index
            &&& l4_index != scheduler_index
            &&& l4_index != cpu_set_index
            &&& l4_index != process_index
            &&& l4_index != pagetable_index
        }) by { reveal(Seq::no_duplicates); };
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        assert(container_head != pcid_allocator_head) by { page_ptr2page_index_neq(container_page, pcid_allocator_page); };
        distinct_2m_heads_have_disjoint_tails(container_head, pcid_allocator_head);
        assert(!page_2m_tail_indices(container_head).contains(pcid_allocator_head) && !page_2m_tail_indices(pcid_allocator_head).contains(container_head)) by {
            page_2m_all_ptrs_contains_head(container_head); page_2m_all_ptrs_contains_head(pcid_allocator_head); distinct_2m_heads_have_disjoint_all_ptrs(container_head, pcid_allocator_head);
            if page_2m_tail_indices(container_head).contains(pcid_allocator_head) { page_2m_all_ptrs_contains_index(container_head, pcid_allocator_head); }
            if page_2m_tail_indices(pcid_allocator_head).contains(container_head) { page_2m_all_ptrs_contains_index(pcid_allocator_head, container_head); }
        };
        assert(krnl.pg_arr.inv()) by { page_array_wf_map(krnl.pg_arr); };
        assert({
            &&& krnl.ctn_mp.view().spec_index(parent_ctn_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(parent_ctn_ptr).addr() == parent_ctn_ptr
            &&& krnl.ctn_mp.spec_index(parent_ctn_ptr).is_init()
            &&& krnl.ctn_mp.spec_index(parent_ctn_ptr).view_ghost().uppertree_seq.view().no_duplicates()
            &&& krnl.ctn_mp.spec_index(parent_ctn_ptr).view_ghost().uppertree_seq.view().len() == krnl.ctn_mp.spec_index(parent_ctn_ptr).view_rodata().view().depth
        }) by { container_perms_wf_at(krnl.ctn_mp, parent_ctn_ptr); };
        assert(bootstrap_pages.contains(allocator_4k_page) && bootstrap_pages.contains(allocator_2m_page) && bootstrap_pages.contains(allocator_1g_page) && bootstrap_pages.contains(scheduler_page)
            && bootstrap_pages.contains(cpu_set_page) && bootstrap_pages.contains(process_page) && bootstrap_pages.contains(pagetable_page) && bootstrap_pages.contains(l4_page)) by {
            bootstrap_seq.to_set_ensures(); reveal(new_container_bootstrap_4k_pages); reveal(Seq::contains);
        };
        assert(krnl.dflt_pt.view().wf()) by { krnl.default_pagetable_view_inv(); };
        assert(pei_valid(krnl.dflt_pt.view().kernel_l4_end)) by { krnl.dflt_pt.view().kernel_l4_end_valid(); };
    }
    let child_depth = krnl.ctn_mp.borrow_rodata(parent_ctn_ptr).borrow().depth + 1;
    let ghost parent_uppers = krnl.ctn_mp.spec_index(parent_ctn_ptr).view_ghost().uppertree_seq.view();
    let ghost child_uppers = parent_uppers.push(parent_ctn_ptr);
    let ghost moved_pages = new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).union(funding_pages.to_set());
    proof {
        assert(!parent_uppers.contains(parent_ctn_ptr)) by { container_uppertree_seq_not_self(krnl.rt_ctn, krnl.ctn_mp, parent_ctn_ptr); };
        assert(child_uppers.no_duplicates()) by { seq_push_absent_implies_no_duplicates_and_index_of::<RwLockContainerPtr>(); };
        assert(child_uppers.to_set().subset_of(krnl.ctn_mp.dom())) by { parent_uppers.to_set_ensures(); child_uppers.to_set_ensures(); seq_push_implies_contains::<RwLockContainerPtr>(); container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, parent_ctn_ptr); };
        assert(!child_uppers.to_set().contains(child_ctn_ptr)) by { child_uppers.to_set_ensures(); };
        owned_4k_page_not_in_2m_region(krnl, thread_page, container_head); owned_4k_page_not_in_2m_region(krnl, thread_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, allocator_4k_page, container_head); owned_4k_page_not_in_2m_tail(krnl, allocator_2m_page, container_head);
        owned_4k_page_not_in_2m_tail(krnl, allocator_1g_page, container_head); owned_4k_page_not_in_2m_tail(krnl, allocator_4k_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, allocator_2m_page, pcid_allocator_head); owned_4k_page_not_in_2m_tail(krnl, allocator_1g_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, scheduler_page, container_head); owned_4k_page_not_in_2m_tail(krnl, scheduler_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, cpu_set_page, container_head); owned_4k_page_not_in_2m_tail(krnl, cpu_set_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, process_page, container_head); owned_4k_page_not_in_2m_tail(krnl, process_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, pagetable_page, container_head); owned_4k_page_not_in_2m_tail(krnl, pagetable_page, pcid_allocator_head);
        owned_4k_page_not_in_2m_tail(krnl, l4_page, container_head); owned_4k_page_not_in_2m_tail(krnl, l4_page, pcid_allocator_head);
        assert({
            &&& !funding_pages.to_set().contains(container_page)
            &&& !funding_pages.to_set().contains(pcid_allocator_page)
            &&& !funding_pages.to_set().contains(allocator_4k_page)
            &&& !funding_pages.to_set().contains(allocator_2m_page)
            &&& !funding_pages.to_set().contains(allocator_1g_page)
            &&& !funding_pages.to_set().contains(scheduler_page)
            &&& !funding_pages.to_set().contains(cpu_set_page)
            &&& !funding_pages.to_set().contains(process_page)
            &&& !funding_pages.to_set().contains(pagetable_page)
            &&& !funding_pages.to_set().contains(l4_page)
        }) by { reveal(new_container_moved_pages); reveal(new_container_bootstrap_4k_pages); };
        assert(staged_4k_page_chain(pre_krnl.pg_arr, funding_pages)) by { reveal(publish_staged_container_root_eof_preconditions); };
    }
    let (funded_global_pool, Tracked(container_perm), Tracked(pcid_allocator_perm), Ghost(pool_page_locks), Ghost(prepared_page_locks)) = prepare_new_container_backing_pages(
        &mut krnl.pg_arr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page,
        cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_page_count, funding_page_head, Ghost(funding_pages),
        Ghost(funding_indices), child_allocator_4k_ptr, child_ctn_ptr, child_depth, Ghost(pre_krnl), Tracked(&*lctx),
        Tracked(funding_page_lock_perms), Tracked(container_page_lock_perm), Tracked(pcid_allocator_page_lock_perm),
        Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    let allocator_4k_value = PageAllocator::<ALLOCATOR_SIZE_4K>::new_with_global_pool(child_ctn_ptr, child_depth, funded_global_pool, allocator_quota_4k);
    let allocator_2m_value = PageAllocator::<ALLOCATOR_SIZE_2M>::new_empty(child_ctn_ptr, child_depth);
    let allocator_1g_value = PageAllocator::<ALLOCATOR_SIZE_1G>::new_empty(child_ctn_ptr, child_depth);
    let scheduler_value = Scheduler::new_empty(child_ctn_ptr);
    let mut pcid_allocator_value = PcidAllocator::new_empty(child_ctn_ptr, child_depth);
    pcid_allocator_value.alloc(root_pcid, child_prc_ptr);
    let (Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Ghost(process_page_locks)) = publish_new_container_process_and_pagetable(
        krnl, child_ctn_ptr, child_prc_ptr, child_pagetable_ptr, l4_page, root_pcid, child_depth, process_quota_4k,
        container_head, pcid_allocator_head, Ghost(prepared_page_locks), Tracked(&mut *lctx), Tracked(process_page_lock_perm),
        Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    let Ghost(allocator_page_locks) = publish_new_container_allocators(
        krnl, child_ctn_ptr, allocator_4k_page, allocator_2m_page, allocator_1g_page, allocator_4k_value, allocator_2m_value,
        allocator_1g_value, container_head, pcid_allocator_head, Ghost(process_page_locks), Tracked(&*lctx),
        Tracked(allocator_4k_page_lock_perm), Tracked(allocator_2m_page_lock_perm), Tracked(allocator_1g_page_lock_perm),
        Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    let Ghost(scheduler_page_locks) = publish_new_container_scheduler(
        krnl, child_ctn_ptr, child_sched_ptr, scheduler_page, scheduler_value, container_head, pcid_allocator_head, Ghost(allocator_page_locks),
        Tracked(&*lctx), Tracked(scheduler_page_lock_perm), Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    let cpu_set_value = CpuSet::new_empty(child_ctn_ptr, child_depth);
    let (Tracked(child_cpu_set_lock_perm), Ghost(cpu_set_page_locks)) = publish_new_container_cpu_set(
        krnl, child_ctn_ptr, child_cpu_set_ptr, cpu_set_page, cpu_set_value, container_head, pcid_allocator_head,
        Ghost(scheduler_page_locks), Tracked(&mut *lctx), Tracked(cpu_set_page_lock_perm), Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    let mut container_value = Container::new_staged(child_ctn_ptr, child_prc_ptr, child_depth);
    container_value.owned_pages = Ghost(moved_pages);
    let container_rodata = ReadOnlyNode::new(
        ContainerRO {
            parent: Some(parent_ctn_ptr), depth: child_depth, scheduler: child_sched_ptr, pcid_allocator: child_pcid_allc_ptr,
            cpu_set: child_cpu_set_ptr, allocator_ptr_4k: child_allocator_4k_ptr, allocator_ptr_2m: child_allocator_2m_ptr, allocator_ptr_1g: child_allocator_1g_ptr,
        },
        Ghost(child_ctn_ptr),
    );
    let container_ghost = ContainerGhost {
        uppertree_seq: Ghost(child_uppers), subtree_set: Ghost(Set::empty()), owned_processes: Ghost(Set::empty().insert(child_prc_ptr)),
        owned_threads: Ghost(Set::empty()), owned_indirect_threads: Ghost(Set::empty()), owned_endpoints: Ghost(Set::empty()), retire_ready: false,
    };
    proof {
        assert(!old(krnl).cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(child_ctn_ptr))) by {
            container_cpu_offline_flags_wf_flags_at(old(krnl).ctn_mp, old(krnl).cpu_offline_mp, cpu_offline_flags_ptr(child_ctn_ptr));
            let owner = old(krnl).cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child_ctn_ptr)).owning_container.view();
            assert(old(krnl).cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(child_ctn_ptr)) ==> old(krnl).ctn_mp.dom().contains(owner) && page_ptr_2m_valid(owner) && cpu_offline_flags_ptr(owner) == cpu_offline_flags_ptr(child_ctn_ptr)) by {
                container_pages_backward_at(old(krnl).pg_arr, old(krnl).ctn_mp, owner);
            };
        };
    }
    let (Tracked(child_pcid_allocator_lock_perm), Tracked(child_container_lock_perm)) = publish_new_container_pcid_allocator_and_container(
        krnl, child_pcid_allc_ptr, pcid_allocator_value, child_ctn_ptr, container_value, container_rodata, container_ghost,
        Ghost(allocator_4k_page), Ghost(allocator_2m_page), Ghost(allocator_1g_page), Ghost(scheduler_page), Ghost(cpu_set_page), Ghost(child_prc_ptr),
        Ghost(child_pagetable_ptr), Ghost(l4_page), Ghost(bootstrap_seq), Ghost(funding_pages), Ghost(funding_indices), Ghost(pool_page_locks),
        Ghost(cpu_set_page_locks), Tracked(&mut *lctx), Tracked(pcid_allocator_perm), Tracked(container_perm),
    );
    proof {
        assert(lctx.container_lock_map().dom().contains(parent_ctn_ptr));
        assert({
            &&& moved_pages.subset_of(pre_krnl.ctn_mp.spec_index(parent_ctn_ptr).view().owned_pages.view())
            &&& !moved_pages.contains(thread_page)
            &&& pre_krnl.ctn_mp.spec_index(parent_ctn_ptr).view().owned_pages.view().contains(thread_page)
        }) by { reveal(publish_staged_container_root_eof_preconditions); };
    }
    link_new_container_into_tree(
        &mut krnl.ctn_mp, krnl.rt_ctn, parent_ctn_ptr, child_ctn_ptr, child_prc_ptr, child_sched_ptr,
        child_pcid_allc_ptr, child_cpu_set_ptr, child_allocator_4k_ptr, child_allocator_2m_ptr, child_allocator_1g_ptr, child_depth,
        thread_page, Ghost(child_uppers), Ghost(moved_pages), Ghost(pre_krnl.ctn_mp), Ghost(pre_krnl.pg_arr), Tracked(&*lctx),
        Tracked(parent_container_lock_perm), Tracked(&child_container_lock_perm),
    );
    proof {
        let ghost consumed_4k_pages = bootstrap_pages.union(funding_pages.to_set());
        let ghost initial_cache = krnl.thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_4k.view();
        assert(initial_cache == consumed_4k_pages.insert(thread_page)) by { reveal(publish_staged_container_root_eof_preconditions); vstd::set::axiom_set_ext_equal(initial_cache, consumed_4k_pages.insert(thread_page)); };
        funding_pages.unique_seq_to_set();
        assert(bootstrap_pages.disjoint(funding_pages.to_set())) by { reveal(new_container_moved_pages); };
        vstd::set_lib::lemma_set_disjoint_lens(bootstrap_pages, funding_pages.to_set()); vstd::set::lemma_set_insert_len(consumed_4k_pages, thread_page);
        assert(funding_page_count < krnl.thrd_mp.spec_index(current_thrd_ptr).view().quota_4k - 8) by { thread_perms_wf_at(krnl.thrd_mp, current_thrd_ptr); };
        let ghost initial_2m_cache = krnl.thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_2m.view();
        assert(initial_2m_cache =~= set![container_page, pcid_allocator_page]) by { reveal(publish_staged_container_root_eof_preconditions); vstd::set::axiom_set_ext_equal(initial_2m_cache, set![container_page, pcid_allocator_page]); };
    }
    thread_map_consume_new_container_staging(&mut krnl.thrd_mp, current_thrd_ptr, thread_page, funding_page_count, Ghost(bootstrap_pages.union(funding_pages.to_set())), Tracked(&*lctx), Tracked(current_thread_lock_perm));
    proof {
        assert(publish_staged_container_root_eof_transition_framing(
            pre_krnl, *krnl, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
            allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
            funding_pages, allocator_quota_4k, process_quota_4k,
        )) by {
            reveal(publish_staged_container_root_eof_transition_framing);
            old(krnl).thrd_mp.typed_lock_map_aligned_write_at(old(lctx).thread_lock_map(), old(lctx).thread_id(), current_thrd_ptr);
        };
    }
    (Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_pcid_allocator_lock_perm), Tracked(child_cpu_set_lock_perm))
}

pub fn publish_staged_container_root(
    krnl: &mut KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_page_count: usize, funding_page_head: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>, allocator_quota_4k: usize,
    process_quota_4k: usize, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(parent_container_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(container_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_4k_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_2m_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_1g_page_lock_perm): Tracked<&LockPerm>,
    Tracked(scheduler_page_lock_perm): Tracked<&LockPerm>, Tracked(cpu_set_page_lock_perm): Tracked<&LockPerm>,
    Tracked(process_page_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<&LockPerm>, Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).ctn_mp.dom().contains(parent_ctn_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_ctn_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_ctn_ptr).being_killed(),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_ctn_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.spec_index(parent_ctn_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        old(krnl).thrd_mp.dom().contains(current_thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
        !old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_container == parent_ctn_ptr,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_4k >= 8,
        funding_page_count <= old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_4k - 8,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_2m >= 2,
        forall|pg_ptr: PagePtr|
            #![trigger old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr)]
            #![trigger funding_pages.to_set().contains(pg_ptr)]
            #![trigger new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(pg_ptr)]
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr) <==> new_container_bootstrap_4k_pages(
                allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
            ).contains(pg_ptr) || funding_pages.to_set().contains(pg_ptr) || pg_ptr == thread_page,
        forall|pg_ptr: PagePtr|
            #![trigger old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr)]
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr) <==> pg_ptr == container_page || pg_ptr == pcid_allocator_page,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().free_quota_pending_clean(),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).len() == 8,
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(thread_page),
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        process_quota_4k <= funding_page_count,
        allocator_quota_4k == funding_page_count - process_quota_4k,
        !funding_pages.to_set().contains(thread_page),
        funding_pages.to_set().disjoint(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page)),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        new_container_moved_pages(
            container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).union(funding_pages.to_set()).subset_of(old(krnl).ctn_mp.spec_index(parent_ctn_ptr).view().owned_pages.view(),),
        !old(krnl).ctn_mp.dom().contains(container_page),
        !old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        !old(krnl).allc_4k_mp.dom().contains(allocator_4k_page),
        !old(krnl).allc_2m_mp.dom().contains(allocator_2m_page),
        !old(krnl).allc_1g_mp.dom().contains(allocator_1g_page),
        !old(krnl).sched_mp.dom().contains(scheduler_page),
        !old(krnl).cpu_set_mp.dom().contains(cpu_set_page),
        !old(krnl).prc_mp.dom().contains(process_page),
        !old(krnl).pt_mp.dom().contains(pagetable_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().owning_container == parent_ctn_ptr,
        forall|pg_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(pg_ptr)]
            funding_page_lock_perms.dom().contains(pg_ptr) ==> {
                &&& page_ptr_valid(pg_ptr)
                &&& funding_page_lock_perms.spec_index(pg_ptr).state() is WriteLock
                &&& funding_page_lock_perms.spec_index(pg_ptr).thread_id() == old(lctx).thread_id()
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr })
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr),).view().view().owning_container == parent_ctn_ptr
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(pg_ptr).lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr),).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(pcid_allocator_page),),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_4k_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_2m_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_1g_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        scheduler_page_lock_perm.state() is WriteLock,
        cpu_set_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_page_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
    ensures
        final(krnl).ctn_mp.spec_index(container_page).locking_thread() is Write,
        final(krnl).pt_mp.spec_index(pagetable_page).locking_thread() is Write,
        final(krnl).cpu_set_mp.spec_index(cpu_set_page).locking_thread() is Write,
        publish_staged_container_root_eof_transition_framing(
            *old(krnl), *final(krnl), parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
            allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
            funding_pages, allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            *old(krnl), parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(krnl).inv(),
        final(krnl).cpu_tlb == old(krnl).cpu_tlb,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).pcid_needflush == old(krnl).pcid_needflush,
        final(krnl).cpu_hw_cr3_pcid == old(krnl).cpu_hw_cr3_pcid,
        final(krnl).cpu_op == old(krnl).cpu_op,
        final(krnl).ep_mp == old(krnl).ep_mp,
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom().insert(allocator_4k_page),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom().insert(allocator_2m_page),
        final(krnl).allc_1g_mp.dom() == old(krnl).allc_1g_mp.dom().insert(allocator_1g_page),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }),
        !final(krnl).ctn_mp.spec_index(container_page).being_killed(),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().parent == Some(parent_ctn_ptr),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().scheduler == scheduler_page,
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().allocator_ptr_4k == allocator_4k_page,
        final(krnl).ctn_mp.spec_index(container_page).view_ghost().owned_processes.view() == set![process_page],
        final(krnl).ctn_mp.spec_index(container_page).view().root_process == process_page,
        !final(krnl).prc_mp.spec_index(process_page).being_killed(),
        !final(krnl).prc_mp.spec_index(process_page).view().zombie,
        final(krnl).prc_mp.spec_index(process_page).view().state.view() is Creating,
        final(krnl).prc_mp.spec_index(process_page).view_rodata().view().owning_container == container_page,
        final(krnl).prc_mp.spec_index(process_page).view_rodata().view().pagetable == pagetable_page,
        final(krnl).prc_mp.spec_index(process_page).view().quota_4k == process_quota_4k,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).owning_container == container_page,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).global_pool.view().view() == funding_pages,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).total_free_pages.view() == funding_page_count,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).quota.view().view() == allocator_quota_4k,
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_page).is_empty(),
        final(krnl).pt_mp.spec_index(pagetable_page).view().proc_ptr == process_page,
        final(krnl).prc_mp.spec_index(process_page).view().iommu_table is None,
        final(krnl).ctn_mp.spec_index(container_page).view_ghost().uppertree_seq.view() == old(krnl).ctn_mp.spec_index(parent_ctn_ptr).view_ghost().uppertree_seq.view().push(parent_ctn_ptr),
        final(krnl).ctn_mp.spec_index(parent_ctn_ptr).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(parent_ctn_ptr).view_ghost().uppertree_seq,
        final(krnl).ctn_mp.spec_index(parent_ctn_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(parent_ctn_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().cpu_set == cpu_set_page,
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_4k.view() == set![thread_page],
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_1g == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_1g,
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().free_quota_pending_fields_unchanged(&old(krnl).thrd_mp.spec_index(current_thrd_ptr).view(),),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view() == (Thread {
            quota_4k: final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_4k, quota_2m: final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_2m,
            temp_alloc_cache_4k: final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_4k, temp_alloc_cache_2m: final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_cache_2m,
            ..old(krnl).thrd_mp.spec_index(current_thrd_ptr).view()
        }),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_container == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_container,
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_proc == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_proc,
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().proc_pagetable_ptr == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().proc_pagetable_ptr,
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state,
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_4k == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_4k - 8 - funding_page_count,
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_2m == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_2m - 2,
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx),),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx),),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx),),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(thread_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(thread_page)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thrd_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().owning_container == parent_ctn_ptr,
        final(krnl).ctn_mp.dom().contains(parent_ctn_ptr),
        !final(krnl).ctn_mp.spec_index(parent_ctn_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(parent_ctn_ptr).view().owned_pages.view().contains(thread_page),
        final(krnl).ctn_mp.spec_index(parent_ctn_ptr).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(parent_ctn_ptr).view_ghost().owned_processes,
        !final(krnl).ctn_mp.spec_index(container_page).view().owned_pages.view().contains(thread_page),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_ctn_ptr).locking_thread()->Write_lock_id,
        current_thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        page_2m_tail_indices(page_ptr2page_index(container_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(allocator_4k_page),
            page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page), page_ptr2page_index(scheduler_page),
            page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page), page_ptr2page_index(pagetable_page),
            page_ptr2page_index(l4_page), page_ptr2page_index(thread_page),
        ],),
        page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(allocator_4k_page),
            page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page), page_ptr2page_index(scheduler_page),
            page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page), page_ptr2page_index(pagetable_page),
            page_ptr2page_index(l4_page), page_ptr2page_index(thread_page),
        ],),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map().dom() == old(lctx).container_lock_map().dom().insert(container_page),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(lctx).container_lock_map().get(ptr)]
            #![trigger final(lctx).container_lock_map().spec_index(ptr)]
            #![trigger old(lctx).container_lock_map().get(ptr)]
            #![trigger old(lctx).container_lock_map().spec_index(ptr)]
            old(lctx).container_lock_map().dom().contains(ptr) && ptr != container_page ==> final(lctx).container_lock_map().get(ptr) == old(lctx).container_lock_map().get(ptr),
        final(lctx).process_lock_map().dom() == old(lctx).process_lock_map().dom().insert(process_page),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(lctx).process_lock_map().get(ptr)]
            #![trigger final(lctx).process_lock_map().spec_index(ptr)]
            #![trigger old(lctx).process_lock_map().get(ptr)]
            #![trigger old(lctx).process_lock_map().spec_index(ptr)]
            old(lctx).process_lock_map().dom().contains(ptr) && ptr != process_page ==> final(lctx).process_lock_map().get(ptr) == old(lctx).process_lock_map().get(ptr),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().insert(pcid_allocator_page),
        final(lctx).cpu_set_lock_map().dom() == old(lctx).cpu_set_lock_map().dom().insert(cpu_set_page),
        forall|ptr: RwLockCpuSetPtr|
            #![trigger final(lctx).cpu_set_lock_map().get(ptr)]
            #![trigger final(lctx).cpu_set_lock_map().spec_index(ptr)]
            #![trigger old(lctx).cpu_set_lock_map().get(ptr)]
            #![trigger old(lctx).cpu_set_lock_map().spec_index(ptr)]
            old(lctx).cpu_set_lock_map().dom().contains(ptr) && ptr != cpu_set_page ==> final(lctx).cpu_set_lock_map().get(ptr) == old(lctx).cpu_set_lock_map().get(ptr),
        final(lctx).pagetable_lock_map().dom() == old(lctx).pagetable_lock_map().dom().insert(pagetable_page),
        forall|ptr: RwLockPageTableRoot|
            #![trigger final(lctx).pagetable_lock_map().get(ptr)]
            #![trigger final(lctx).pagetable_lock_map().spec_index(ptr)]
            #![trigger old(lctx).pagetable_lock_map().get(ptr)]
            #![trigger old(lctx).pagetable_lock_map().spec_index(ptr)]
            old(lctx).pagetable_lock_map().dom().contains(ptr) && ptr != pagetable_page ==> final(lctx).pagetable_lock_map().get(ptr) == old(lctx).pagetable_lock_map().get(ptr),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(krnl).ctn_mp.dom().contains(container_page),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        final(krnl).prc_mp.dom().contains(process_page),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_page, TypedLockMode::Write),
        final(krnl).pt_mp.dom().contains(pagetable_page),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_page, TypedLockMode::Write),
        staged_4k_page_chain(final(krnl).pg_arr, funding_pages),
        final(krnl).sched_mp.dom().contains(scheduler_page),
        final(krnl).cpu_set_mp.dom().contains(cpu_set_page),
        final(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allocator_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), cpu_set_page, TypedLockMode::Write),
        final(krnl).thrd_mp.dom().contains(current_thrd_ptr),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        container_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        scheduler_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(process_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().locking_thread()->Write_lock_id,
        forall|pg_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(pg_ptr)]
            funding_page_lock_perms.dom().contains(pg_ptr) ==> {
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allocator_4k_page), state: FreePageAllocatorState::GlobalList })
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr),).view().view().owning_container == container_page
                &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(pg_ptr).lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr),).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), page_ptr2page_index(pcid_allocator_page),),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).ctn_mp.spec_index(container_page).locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).prc_mp.spec_index(process_page).locking_thread()->Write_lock_id,
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable_page).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).pcid_allc_mp.spec_index(pcid_allocator_page).locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).cpu_set_mp.spec_index(cpu_set_page).locking_thread()->Write_lock_id,
{
    let ghost pre_krnl = *krnl;
    proof {
        assert(publish_staged_container_root_eof_preconditions(
            pre_krnl, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        )) by {
            reveal(publish_staged_container_root_eof_preconditions); reveal(new_container_moved_pages);
            page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
            owned_4k_page_not_in_2m_region(krnl, thread_page, page_ptr2page_index(container_page)); owned_4k_page_not_in_2m_region(krnl, thread_page, page_ptr2page_index(pcid_allocator_page));
            container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_ptr2page_index(thread_page));
        };
    }
    let ret = publish_staged_container_root_mutation(
        krnl, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_page_count,
        funding_page_head, Ghost(funding_pages), allocator_quota_4k, process_quota_4k, Tracked(&mut *lctx),
        Tracked(parent_container_lock_perm), Tracked(current_thread_lock_perm), Tracked(container_page_lock_perm),
        Tracked(pcid_allocator_page_lock_perm), Tracked(allocator_4k_page_lock_perm), Tracked(allocator_2m_page_lock_perm),
        Tracked(allocator_1g_page_lock_perm), Tracked(scheduler_page_lock_perm), Tracked(cpu_set_page_lock_perm),
        Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(funding_page_lock_perms),
        Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    proof {
        publish_staged_container_root_eof_postconditions(
            pre_krnl, *krnl, *old(lctx), parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page,
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page,
            l4_page, thread_page, funding_pages, allocator_quota_4k, process_quota_4k,
            *parent_container_lock_perm, *current_thread_lock_perm, *lctx, *funding_page_lock_perms,
        );
        publish_staged_container_root_eof_inv(
            pre_krnl, *krnl, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
            allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
            funding_pages, allocator_quota_4k, process_quota_4k,
        );
    }
    proof {
        assert(krnl.ctn_mp.spec_index(container_page).locking_thread() is Write) by { krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container_page); };
        assert(krnl.pt_mp.spec_index(pagetable_page).locking_thread() is Write) by { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_page); };
        assert(krnl.cpu_set_mp.spec_index(cpu_set_page).locking_thread() is Write) by { krnl.cpu_set_mp.typed_lock_map_aligned_write_at(lctx.cpu_set_lock_map(), lctx.thread_id(), cpu_set_page); };
    }
    ret
}
}
