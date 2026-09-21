use vstd::assert_sets_equal;
use vstd::prelude::*;
use crate::*;
use super::staged_4k_page_chain::{
    cleanup_published_4k_page_chain,
    page_ptrs_to_indices_excludes_distinct_valid_page,
};
#[cfg(not(feature = "split-crates"))]
use crate::implementation::create_thread_from_staged_page::
    create_thread_from_staged_page_merged;
use super::*;

verus! {
#[verifier::rlimit(15)]
#[verifier::spinoff_prover]
pub(super) fn publish_new_container_base(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, caller_cpu_id: CpuId,
    parent_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot,
    pages_4k: &ArrayVec<PagePtr, 9>, container_page: PagePtr, pcid_allocator_page: PagePtr,
    funding_page_count: usize, funding_page_head: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>,
    allocator_quota_4k: usize, process_quota_4k: usize,
    Tracked(page_4k_lock_perms): Tracked<Map<PagePtr, LockPerm>>,
    Tracked(funding_page_lock_perms): Tracked<Map<PagePtr, LockPerm>>,
    Tracked(container_page_lock_perm): Tracked<LockPerm>, Tracked(pcid_allocator_page_lock_perm): Tracked<LockPerm>,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, caller_cpu_id),
        pages_4k.wf(),
        pages_4k.len() == 9,
        pages_4k.view().no_duplicates(),
        page_4k_lock_perms.dom() == pages_4k.view().to_set(),
        allocated_4k_page_lock_perms_wf(page_4k_lock_perms, old(krnl), old(lctx), current_thread_ptr, parent_container_ptr),
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        allocated_4k_page_lock_perms_wf(funding_page_lock_perms, old(krnl), old(lctx), current_thread_ptr, parent_container_ptr),
        funding_pages.to_set().disjoint(pages_4k.view().to_set()),
        process_quota_4k <= funding_page_count,
        allocator_quota_4k == funding_page_count - process_quota_4k,
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(container_page)),
        ),
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)),
        ),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page, pcid_allocator_page, pages_4k.view().spec_index(0), pages_4k.view().spec_index(1),
            pages_4k.view().spec_index(2), pages_4k.view().spec_index(3), pages_4k.view().spec_index(8),
            pages_4k.view().spec_index(4), pages_4k.view().spec_index(5), pages_4k.view().spec_index(6),
        )),
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        new_container_moved_pages(
            container_page, pcid_allocator_page, pages_4k.view().spec_index(0), pages_4k.view().spec_index(1),
            pages_4k.view().spec_index(2), pages_4k.view().spec_index(3), pages_4k.view().spec_index(8),
            pages_4k.view().spec_index(4), pages_4k.view().spec_index(5), pages_4k.view().spec_index(6),
        ).union(funding_pages.to_set()).subset_of(
            old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view(),
        ),
        !old(krnl).ctn_mp.dom().contains(container_page),
        !old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        !old(krnl).allc_4k_mp.dom().contains(pages_4k.view().spec_index(0)),
        !old(krnl).allc_2m_mp.dom().contains(pages_4k.view().spec_index(1)),
        !old(krnl).allc_1g_mp.dom().contains(pages_4k.view().spec_index(2)),
        !old(krnl).sched_mp.dom().contains(pages_4k.view().spec_index(3)),
        !old(krnl).cpu_set_mp.dom().contains(pages_4k.view().spec_index(8)),
        !old(krnl).prc_mp.dom().contains(pages_4k.view().spec_index(4)),
        !old(krnl).pt_mp.dom().contains(pages_4k.view().spec_index(5)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().owning_container == parent_container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().owning_container == parent_container_ptr,
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 8,
        funding_page_count
            <= old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 8,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m >= 2,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_4k.view()
            =~= pages_4k.view().to_set().union(funding_pages.to_set()),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view() =~= set![container_page, pcid_allocator_page],
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().owning_container == parent_container_ptr,
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom()
            == page_ptrs_to_indices(pages_4k.view())
                .union(page_ptrs_to_indices(funding_pages))
                .union(seq![
                    page_ptr2page_index(container_page),
                    page_ptr2page_index(pcid_allocator_page),
                ].to_set()),
        old(lctx).page_lock_map().dom().disjoint(page_2m_tail_indices(page_ptr2page_index(container_page)).union(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)))),
        old(lctx).lock_id_acyclic(merged_page_lock_id((page_ptr2page_index(container_page) + 1) as usize)),
        old(lctx).lock_id_acyclic(merged_page_lock_id((page_ptr2page_index(pcid_allocator_page) + 1) as usize)),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        pagetable_tlb_entries_present(
            old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush,
            source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view(),
        ) ==> pagetable_tlb_entries_present(
            final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush,
            source_pagetable_ptr, final(krnl).pt_mp.spec_index(source_pagetable_ptr).view(),
        ),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pages_4k.view().spec_index(5), final(krnl).pt_mp.spec_index(pages_4k.view().spec_index(5)).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(pages_4k.view().spec_index(7))],
        final(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        final(lctx).container_lock_map().dom() =~= set![parent_container_ptr, container_page],
        final(lctx).process_lock_map().dom() =~= set![parent_process_ptr, pages_4k.view().spec_index(4)],
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        final(lctx).endpoint_lock_map().dom().is_empty(),
        final(lctx).scheduler_lock_map().dom() =~= set![pages_4k.view().spec_index(3)],
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, pages_4k.view().spec_index(5)],
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        final(krnl).ctn_mp.dom().contains(parent_container_ptr),
        final(krnl).prc_mp.dom().contains(parent_process_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !final(krnl).cpu_arr.spec_index(caller_cpu_id).view().being_killed(),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes.view().contains(parent_process_ptr),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !final(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        final(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        final(krnl).ctn_mp.dom().contains(container_page),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().parent == Some(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().scheduler == pages_4k.view().spec_index(3),
        final(krnl).ctn_mp.spec_index(container_page).view().owned_processes.view().contains(pages_4k.view().spec_index(4)),
        !final(krnl).ctn_mp.spec_index(container_page).being_killed(),
        final(krnl).prc_mp.dom().contains(pages_4k.view().spec_index(4)),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), pages_4k.view().spec_index(4), TypedLockMode::Write),
        !final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).being_killed(),
        !final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).view().zombie,
        final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).view_rodata().view().owning_container == container_page,
        final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).view_rodata().view().pagetable == pages_4k.view().spec_index(5),
        final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).view().quota_4k == process_quota_4k,
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().allocator_ptr_4k == pages_4k.view().spec_index(0),
        final(krnl).allc_4k_mp.dom().contains(pages_4k.view().spec_index(0)),
        final(krnl).allc_4k_mp.spec_index(pages_4k.view().spec_index(0)).owning_container == container_page,
        final(krnl).allc_4k_mp.spec_index(pages_4k.view().spec_index(0)).global_pool.view().view().len() == funding_page_count,
        final(krnl).allc_4k_mp.spec_index(pages_4k.view().spec_index(0)).total_free_pages.view() == funding_page_count,
        final(krnl).allc_4k_mp.spec_index(pages_4k.view().spec_index(0)).quota.view().view() == funding_page_count - process_quota_4k,
        final(krnl).pt_mp.dom().contains(pages_4k.view().spec_index(5)),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pages_4k.view().spec_index(5), TypedLockMode::Write),
        final(krnl).sched_mp.dom().contains(pages_4k.view().spec_index(3)),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), pages_4k.view().spec_index(3), TypedLockMode::Write),
        !final(krnl).sched_mp.spec_index(pages_4k.view().spec_index(3)).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![pages_4k.view().spec_index(7)],
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        !final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 8 - funding_page_count,
        page_ptr_valid(pages_4k.view().spec_index(7)),
        page_ptr_valid(pages_4k.view().spec_index(8)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))).view().view().owning_container == parent_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(7)), TypedLockMode::Write),
        !final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))).view().being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(pages_4k.view().spec_index(7)),
        !final(krnl).ctn_mp.spec_index(container_page).view().owned_pages.view().contains(pages_4k.view().spec_index(7)),
        source_pagetable_ptr != pages_4k.view().spec_index(5),
        final(krnl).cpu_arr.spec_index(caller_cpu_id).view() == old(krnl).cpu_arr.spec_index(caller_cpu_id).view(),
        final(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread() == old(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread(),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread(),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).ctn_mp.spec_index(container_page).locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).locking_thread()->Write_lock_id,
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).pt_mp.spec_index(pages_4k.view().spec_index(5)).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).sched_mp.spec_index(pages_4k.view().spec_index(3)).locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))).view().locking_thread()->Write_lock_id,
{
    // This long publish equation expands sequence membership repeatedly; reveal it only in the scoped set proof below.
    hide(Seq::contains);
    let allocator_4k_page = *pages_4k.get(0);
    let allocator_2m_page = *pages_4k.get(1);
    let allocator_1g_page = *pages_4k.get(2);
    let scheduler_page = *pages_4k.get(3);
    let cpu_set_page = *pages_4k.get(8);
    let process_page = *pages_4k.get(4);
    let pagetable_page = *pages_4k.get(5);
    let l4_page = *pages_4k.get(6);
    let thread_page = *pages_4k.get(7);
    proof {
        new_container_page_positions(pages_4k.view());
        assert({
            &&& page_ptr_valid(allocator_4k_page)
            &&& page_ptr_valid(allocator_2m_page)
            &&& page_ptr_valid(allocator_1g_page)
            &&& page_ptr_valid(scheduler_page)
            &&& page_ptr_valid(process_page)
            &&& page_ptr_valid(pagetable_page)
            &&& page_ptr_valid(l4_page)
            &&& page_ptr_valid(thread_page)
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(process_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(l4_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
        }) by {
            pages_4k.view().to_set_ensures();
        };
    }
    let tracked mut page_4k_lock_perms = page_4k_lock_perms;
    let tracked allocator_4k_page_lock_perm = page_4k_lock_perms.tracked_remove(allocator_4k_page);
    let tracked allocator_2m_page_lock_perm = page_4k_lock_perms.tracked_remove(allocator_2m_page);
    let tracked allocator_1g_page_lock_perm = page_4k_lock_perms.tracked_remove(allocator_1g_page);
    let tracked scheduler_page_lock_perm = page_4k_lock_perms.tracked_remove(scheduler_page);
    let tracked cpu_set_page_lock_perm = page_4k_lock_perms.tracked_remove(cpu_set_page);
    let tracked process_page_lock_perm = page_4k_lock_perms.tracked_remove(process_page);
    let tracked pagetable_page_lock_perm = page_4k_lock_perms.tracked_remove(pagetable_page);
    let tracked l4_page_lock_perm = page_4k_lock_perms.tracked_remove(l4_page);
    let tracked thread_page_lock_perm = page_4k_lock_perms.tracked_remove(thread_page);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    let (Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms)) = wlock_new_container_2m_page_tails(krnl, Tracked(&mut *lctx), container_head, pcid_allocator_head);
    proof {
        assert({
            &&& krnl.pg_arr.spec_index(container_head) == old(krnl).pg_arr.spec_index(container_head)
            &&& krnl.pg_arr.spec_index(pcid_allocator_head) == old(krnl).pg_arr.spec_index(pcid_allocator_head)
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(scheduler_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(process_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(l4_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(thread_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page))
        });
        assert(staged_4k_page_chain(krnl.pg_arr, funding_pages)) by {
            broadcast use page_ptr_sequence_index_in_equal_set;
            page_ptr_valid_imply_page_index_valid();
        };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
    }
    let ghost lctx_before_publish = *lctx;
    let (Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_scheduler_lock_perm), Tracked(child_pcid_allocator_lock_perm)) = publish_staged_container_root(
        krnl, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page,
        allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page, thread_page, funding_page_count, funding_page_head,
        Ghost(funding_pages), allocator_quota_4k, process_quota_4k, Tracked(&mut *lctx),
        Tracked(parent_container_lock_perm), Tracked(current_thread_lock_perm),
        Tracked(&container_page_lock_perm), Tracked(&pcid_allocator_page_lock_perm),
        Tracked(&allocator_4k_page_lock_perm), Tracked(&allocator_2m_page_lock_perm),
        Tracked(&allocator_1g_page_lock_perm), Tracked(&scheduler_page_lock_perm),
        Tracked(&cpu_set_page_lock_perm), Tracked(&process_page_lock_perm), Tracked(&pagetable_page_lock_perm), Tracked(&l4_page_lock_perm),
        Tracked(&funding_page_lock_perms), Tracked(&container_tail_lock_perms), Tracked(&pcid_allocator_tail_lock_perms),
    );
    proof {
        assert({
            &&& parent_container_ptr != container_page
            &&& parent_process_ptr != process_page
            &&& source_pagetable_ptr != pagetable_page
            &&& lctx_before_publish.container_lock_map() == old(lctx).container_lock_map()
            &&& lctx_before_publish.process_lock_map() == old(lctx).process_lock_map()
            &&& lctx_before_publish.pagetable_lock_map() == old(lctx).pagetable_lock_map()
        });
        assert(lctx.container_lock_map().get(parent_container_ptr)
            == lctx_before_publish.container_lock_map().get(parent_container_ptr));
        assert(lctx.process_lock_map().get(parent_process_ptr)
            == lctx_before_publish.process_lock_map().get(parent_process_ptr));
        assert(lctx.pagetable_lock_map().get(source_pagetable_ptr)
            == lctx_before_publish.pagetable_lock_map().get(source_pagetable_ptr));
        assert(typed_lock_map_contains_mode(
            lctx.container_lock_map(),
            parent_container_ptr,
            TypedLockMode::Write,
        ));
        assert(typed_lock_map_contains_mode(
            lctx.process_lock_map(),
            parent_process_ptr,
            TypedLockMode::Write,
        ));
        assert(typed_lock_map_contains_mode(
            lctx.pagetable_lock_map(),
            source_pagetable_ptr,
            TypedLockMode::Write,
        ));
        page_2m_all_ptrs_contains_head(container_head);
        page_2m_all_ptrs_contains_head(pcid_allocator_head);
        page_ptr_roundtrip();
        assert(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(container_page)) by { reveal(new_container_moved_pages); };
        assert(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(pcid_allocator_page)) by { reveal(new_container_moved_pages); };
        assert(!funding_pages.to_set().contains(allocator_4k_page)
            && !funding_pages.to_set().contains(allocator_2m_page)
            && !funding_pages.to_set().contains(allocator_1g_page)
            && !funding_pages.to_set().contains(scheduler_page)
            && !funding_pages.to_set().contains(cpu_set_page)
            && !funding_pages.to_set().contains(process_page)
            && !funding_pages.to_set().contains(pagetable_page)
            && !funding_pages.to_set().contains(l4_page)
            && !funding_pages.to_set().contains(thread_page)) by {
            new_container_page_positions(pages_4k.view());
        };
        assert({
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(container_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pcid_allocator_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(allocator_4k_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(allocator_2m_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(allocator_1g_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(scheduler_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(cpu_set_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(process_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pagetable_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(l4_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(thread_page))
        }) by {
            broadcast use page_ptr_sequence_index_in_equal_set;
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, container_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, pcid_allocator_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, allocator_4k_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, allocator_2m_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, allocator_1g_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, scheduler_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, cpu_set_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, process_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, pagetable_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, l4_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, thread_page);
        };
    }
    cleanup_published_4k_page_chain(krnl, funding_page_count, funding_page_head, Ghost(funding_pages), allocator_4k_page, container_page, Tracked(&mut *lctx), Tracked(funding_page_lock_perms));
    proof {
        assert_sets_equal!(
            lctx.page_lock_map().dom()
                .difference(
                    page_2m_tail_indices(container_head)
                        .union(page_2m_tail_indices(pcid_allocator_head))
                        .union(seq![
                            page_ptr2page_index(allocator_4k_page),
                            page_ptr2page_index(allocator_2m_page),
                            page_ptr2page_index(allocator_1g_page),
                            page_ptr2page_index(scheduler_page),
                            page_ptr2page_index(cpu_set_page),
                            page_ptr2page_index(process_page),
                            page_ptr2page_index(pagetable_page),
                            page_ptr2page_index(l4_page),
                            container_head,
                            pcid_allocator_head,
                        ].to_set()),
                )
                == set![page_ptr2page_index(thread_page)],
            page_index => {
                new_container_page_positions(pages_4k.view());
                reveal(Seq::contains);
            }
        );
    }
    let (Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_scheduler_lock_perm), Tracked(thread_page_lock_perm)) = finish_staged_container_publish(
        krnl, Tracked(&mut *lctx), pages_4k, container_page, pcid_allocator_page,
        Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
        Tracked(container_page_lock_perm), Tracked(pcid_allocator_page_lock_perm),
        Tracked(allocator_4k_page_lock_perm), Tracked(allocator_2m_page_lock_perm),
        Tracked(allocator_1g_page_lock_perm), Tracked(scheduler_page_lock_perm),
        Tracked(cpu_set_page_lock_perm), Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm),
        Tracked(l4_page_lock_perm), Tracked(thread_page_lock_perm), Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_scheduler_lock_perm),
        Tracked(child_pcid_allocator_lock_perm),
    );
    proof {
        assert(typed_lock_map_contains_mode(
            lctx.container_lock_map(),
            parent_container_ptr,
            TypedLockMode::Write,
        ));
        assert(typed_lock_map_contains_mode(
            lctx.process_lock_map(),
            parent_process_ptr,
            TypedLockMode::Write,
        ));
        assert(typed_lock_map_contains_mode(
            lctx.pagetable_lock_map(),
            source_pagetable_ptr,
            TypedLockMode::Write,
        ));
        assert(krnl.ctn_mp.spec_index(parent_container_ptr).view().owned_processes.view().contains(parent_process_ptr)) by { reveal(container_process_wf); };
        assert(lctx.holds_no_allocator_locks(PageSize::SZ4k) && lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by { reveal(LocalContext::holds_no_allocator_locks); };
    }
    proof { assert(pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pages_4k.view().spec_index(5), krnl.pt_mp.spec_index(pages_4k.view().spec_index(5)).view())) by { reveal(tlb_wf_spec); }; }
    (Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_scheduler_lock_perm), Tracked(thread_page_lock_perm),)
}

#[verifier::spinoff_prover]
pub(super) fn create_root_thread_and_finish_new_container(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    caller_cpu_id: CpuId, parent_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot,
    child_container_ptr: RwLockContainerPtr, child_process_ptr: RwLockProcessPtr,
    child_pagetable_ptr: RwLockPageTableRoot, child_scheduler_ptr: RwLockSchedulerPtr,
    child_allocator_4k_ptr: RwLockPageAllocatorPtr, thread_page_ptr: PagePtr,
    caller_cpu_lock_perm: Tracked<LockPerm>, parent_container_lock_perm: Tracked<LockPerm>,
    parent_process_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>,
    source_pagetable_lock_perm: Tracked<LockPerm>, child_container_lock_perm: Tracked<LockPerm>,
    child_process_lock_perm: Tracked<LockPerm>, child_pagetable_lock_perm: Tracked<LockPerm>,
    child_scheduler_lock_perm: Tracked<LockPerm>, thread_page_lock_perm: Tracked<LockPerm>, initial_regs: &Registers,
) -> (new_thread_ptr: RwLockThreadPtr)
    requires
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, child_pagetable_ptr, old(krnl).pt_mp.spec_index(child_pagetable_ptr).view()),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        index_valid(NUM_CPUS, caller_cpu_id),
        old(krnl).cpu_published[caller_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_pcid),
        page_ptr_valid(thread_page_ptr),
        parent_container_ptr != child_container_ptr,
        parent_process_ptr != child_process_ptr,
        source_pagetable_ptr != child_pagetable_ptr,
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thread_page_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr, child_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr, child_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom() =~= set![child_scheduler_ptr],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, child_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(caller_cpu_id)
            .view().being_killed(),
        caller_cpu_lock_perm.view().state() is WriteLock,
        caller_cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        caller_cpu_lock_perm.view().lock_id()
            == old(krnl).cpu_arr.spec_index(caller_cpu_id)
                .view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        parent_container_lock_perm.view().state() is WriteLock,
        parent_container_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        parent_container_lock_perm.view().lock_id()
            == old(krnl).ctn_mp.spec_index(parent_container_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr)
            .view_rodata().view().owning_container
            == parent_container_ptr,
        parent_process_lock_perm.view().state() is WriteLock,
        parent_process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_process_lock_perm.view().lock_id()
            == old(krnl).prc_mp.spec_index(parent_process_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_4k.view() == set![thread_page_ptr],
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().quota_4k >= 1,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_clean(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id()
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        source_pagetable_lock_perm.view().state() is WriteLock,
        source_pagetable_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        source_pagetable_lock_perm.view().lock_id()
            == old(krnl).pt_mp.spec_index(source_pagetable_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().parent == Some(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().scheduler == child_scheduler_ptr,
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        old(krnl).allc_4k_mp.dom().contains(child_allocator_4k_ptr),
        child_container_lock_perm.view().state() is WriteLock,
        child_container_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        child_container_lock_perm.view().lock_id()
            == old(krnl).ctn_mp.spec_index(child_container_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(child_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_process_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(child_process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(child_process_ptr)
            .view_rodata().view().owning_container == child_container_ptr,
        old(krnl).prc_mp.spec_index(child_process_ptr)
            .view_rodata().view().pagetable == child_pagetable_ptr,
        child_process_lock_perm.view().state() is WriteLock,
        child_process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_process_lock_perm.view().lock_id()
            == old(krnl).prc_mp.spec_index(child_process_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write),
        child_pagetable_lock_perm.view().state() is WriteLock,
        child_pagetable_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        child_pagetable_lock_perm.view().lock_id()
            == old(krnl).pt_mp.spec_index(child_pagetable_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(child_scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), child_scheduler_ptr, TypedLockMode::Write),
        !old(krnl).sched_mp.spec_index(child_scheduler_ptr).being_killed(),
        child_scheduler_lock_perm.view().state() is WriteLock,
        child_scheduler_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        child_scheduler_lock_perm.view().lock_id()
            == old(krnl).sched_mp.spec_index(child_scheduler_ptr)
                .locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(thread_page_ptr), TypedLockMode::Write),
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr))
            .view().being_killed(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr))
            .view().view().owning_container == parent_container_ptr,
        old(krnl).ctn_mp.spec_index(parent_container_ptr)
            .view().owned_pages.view().contains(thread_page_ptr),
        old(krnl).ctn_mp.spec_index(parent_container_ptr)
            .view().owned_processes.view().contains(parent_process_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .view().owned_processes.view().contains(child_process_ptr),
        thread_page_lock_perm.view().state() is WriteLock,
        thread_page_lock_perm.view().thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.view().lock_id()
            == old(krnl).pg_arr.spec_index(
                page_ptr2page_index(thread_page_ptr),
            ).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(steps).steps == record_user_view_change(old(steps).steps, old(steps).snap_shot, kernel_k_to_kernel_u(*final(krnl))),
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        new_thread_ptr == thread_page_ptr,
        final(krnl).thr_mp.dom().contains(new_thread_ptr),
        final(krnl).thr_mp.spec_index(new_thread_ptr)
            .view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(new_thread_ptr)
            .view().owning_container == child_container_ptr,
        final(krnl).thr_mp.spec_index(new_thread_ptr)
            .view().owning_proc == child_process_ptr,
        final(krnl).ctn_mp.dom().contains(child_container_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().parent
            == old(krnl).ctn_mp.spec_index(child_container_ptr)
                .view_rodata().view().parent,
        final(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        final(krnl).prc_mp.dom().contains(child_process_ptr),
        final(krnl).prc_mp.spec_index(child_process_ptr)
            .view_rodata().view().owning_container
            == old(krnl).prc_mp.spec_index(child_process_ptr)
                .view_rodata().view().owning_container,
        final(krnl).prc_mp.spec_index(child_process_ptr)
            .view().quota_4k
            == old(krnl).prc_mp.spec_index(child_process_ptr)
                .view().quota_4k,
        final(krnl).allc_4k_mp.dom().contains(child_allocator_4k_ptr),
        final(krnl).allc_4k_mp.spec_index(child_allocator_4k_ptr)
            == old(krnl).allc_4k_mp.spec_index(child_allocator_4k_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().quota_4k - 1,
{
    let tracked caller_cpu_lock_perm = caller_cpu_lock_perm.get();
    let tracked parent_container_lock_perm = parent_container_lock_perm.get();
    let tracked parent_process_lock_perm = parent_process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked child_container_lock_perm = child_container_lock_perm.get();
    let tracked child_process_lock_perm = child_process_lock_perm.get();
    let tracked child_pagetable_lock_perm = child_pagetable_lock_perm.get();
    let tracked child_scheduler_lock_perm = child_scheduler_lock_perm.get();
    let tracked thread_page_lock_perm = thread_page_lock_perm.get();
    let ghost caller_quota_4k = krnl.thr_mp
        .spec_index(current_thread_ptr).view().quota_4k;
    transfer_staged_thread_page_to_child(
        krnl, Tracked(&mut *lctx), thread_page_ptr, current_thread_ptr, parent_container_ptr, child_container_ptr,
        Tracked(&thread_page_lock_perm), Tracked(&parent_container_lock_perm), Tracked(&child_container_lock_perm),
    );
    let (
        new_thread_ptr,
        Tracked(new_thread_lock_perm),
    ) = create_thread_from_staged_page_merged(
        krnl,
        thread_page_ptr,
        child_process_ptr,
        current_thread_ptr,
        child_container_ptr,
        child_scheduler_ptr,
        Tracked(&mut *lctx),
        Tracked(&thread_page_lock_perm),
        Tracked(&child_process_lock_perm),
        Tracked(&current_thread_lock_perm),
        Tracked(&child_scheduler_lock_perm),
        initial_regs,
    );

    krnl.wunlock_thread(new_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm));
    krnl.wunlock_process(child_process_ptr, Tracked(&mut *lctx), Tracked(child_process_lock_perm));
    krnl.wunlock_pagetable(child_pagetable_ptr, Tracked(&mut *lctx), Tracked(child_pagetable_lock_perm));
    krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(thread_page_ptr), Tracked(&mut *lctx), Tracked(thread_page_lock_perm));
    krnl.wunlock_scheduler(child_scheduler_ptr, Tracked(&mut *lctx), Tracked(child_scheduler_lock_perm));
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    proof {
        assert(
            krnl.thr_mp.spec_index(current_thread_ptr).view().quota_4k
                == caller_quota_4k - 1
        );
        assert(
            krnl.prc_mp.spec_index(parent_process_ptr)
                .view().owned_threads.view().len() != 0
        ) by {
            reveal(process_thread_wf);
        };
    }
    krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(parent_process_lock_perm));
    proof {
        assert({
            &&& krnl.ctn_mp.spec_index(child_container_ptr)
                .view().owned_processes.view().contains(child_process_ptr)
            &&& krnl.ctn_mp.spec_index(parent_container_ptr)
                .view().owned_processes.view().contains(parent_process_ptr)
            &&& !krnl.ctn_mp.spec_index(child_container_ptr)
                .view().owned_processes.view().is_empty()
            &&& !krnl.ctn_mp.spec_index(parent_container_ptr)
                .view().owned_processes.view().is_empty()
        }) by {
        };
    }
    krnl.wunlock_container(child_container_ptr, Tracked(&mut *lctx), Tracked(child_container_lock_perm));
    krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(parent_container_lock_perm));
    krnl.wunlock_cpu(caller_cpu_id, Tracked(&mut *lctx), Tracked(caller_cpu_lock_perm));
    proof {
        assert(lctx.no_locks_held()) by { reveal(LocalContext::holds_no_allocator_locks); };
        steps.end_kernel_step(&*krnl, &*lctx);
    }
    new_thread_ptr
}

#[verifier::spinoff_prover]
pub(super) fn transfer_staged_thread_page_to_child(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, page_ptr: PagePtr,
    staging_thread_ptr: RwLockThreadPtr, parent_container_ptr: RwLockContainerPtr,
    child_container_ptr: RwLockContainerPtr, Tracked(page_lock_perm): Tracked<&LockPerm>,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(child_container_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        lctx.kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), lctx),
        lock_id_set_aligned(lctx),
        page_ptr_valid(page_ptr),
        parent_container_ptr != child_container_ptr,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(page_ptr),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        child_container_lock_perm.state() is WriteLock,
        child_container_lock_perm.thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(staging_thread_ptr),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == parent_container_ptr,
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        *final(lctx) == *old(lctx),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        !final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().remove(page_ptr),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes == old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_pages.view().insert(page_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_processes == old(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_processes,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().scheduler == old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().scheduler,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k == old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k,
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !final(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        child_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            ctn_mp: final(krnl).ctn_mp,
            ..*old(krnl)
        }),
{
    let ghost pre = *krnl;
    let page_index = page_ptr2page_index(page_ptr);
    proof {
        page_ptr_valid_imply_page_index_valid();
        assert(krnl.pg_arr.inv()) by { reveal(page_array_wf); };
        assert(krnl.pg_arr.spec_index(page_index).view().is_init()) by { reveal(page_array_wf); };
        assert(krnl.ctn_mp.perms_wf()) by { reveal(container_perms_wf); };
        assert(krnl.ctn_mp.spec_index(parent_container_ptr).is_init() && krnl.ctn_mp.spec_index(child_container_ptr).is_init()) by { reveal(container_perms_wf); };
        assert(old(krnl).pg_arr.spec_index(page_index).view().view().inv()) by { reveal(page_array_wf); };
        assert(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().inv() && old(krnl).ctn_mp.spec_index(child_container_ptr).view().inv()) by {
            reveal(container_perms_wf);
        };
    }
    {
        let page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_lock_perm));
        page.owning_container = child_container_ptr;
        proof {
            assert(page.inv()) by {
                assert(old(krnl).pg_arr.spec_index(page_index).view().view().inv()) by { reveal(page_array_wf); };
            };
        }
    }
    {
        let parent = krnl.ctn_mp.borrow_mut_typed(parent_container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(parent_container_lock_perm));
        parent.owned_pages = Ghost(parent.owned_pages.view().remove(page_ptr));
        proof {
            assert(parent.inv()) by {
                assert(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().inv());
            };
        }
    }
    {
        proof {
            assert(krnl.ctn_mp.spec_index(child_container_ptr).is_init()) by { reveal(container_perms_wf); };
        }
        let child = krnl.ctn_mp.borrow_mut_typed(child_container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(child_container_lock_perm));
        child.owned_pages = Ghost(child.owned_pages.view().insert(page_ptr));
        proof {
            assert(child.inv()) by {
                assert(old(krnl).ctn_mp.spec_index(child_container_ptr).view().inv());
            };
        }
    }
    proof {
        assert(staged_4k_page_container_transfer_transition(pre, *krnl, page_ptr, staging_thread_ptr, parent_container_ptr, child_container_ptr)) by {
            reveal(staged_4k_page_container_transfer_transition);
        };
        staged_4k_page_container_transfer_eof(pre, *krnl, page_ptr, staging_thread_ptr, parent_container_ptr, child_container_ptr);
    }
}
}
