use vstd::assert_sets_equal;
use vstd::prelude::*;
use crate::*;
use super::staged_4k_page_chain::cleanup_published_4k_page_chain;
use super::syscall_new_container_publish_indices::new_container_publish_staging_heads;
use super::*;

verus! {
/// Returns the published funding chain to the child allocator, records the sharing progress, and releases the staging page locks.
#[verifier::spinoff_prover]
pub(super) fn release_new_container_publish_staging(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, current_thread_ptr: RwLockThreadPtr, pages_4k: &ArrayVec<PagePtr, 9>,
    container_page: PagePtr, pcid_allocator_page: PagePtr, funding_page_count: usize, funding_page_head: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>,
    Ghost(progress): Ghost<Option<SyscallProgress>>, Tracked(funding_page_lock_perms): Tracked<Map<PagePtr, LockPerm>>,
    Tracked(container_tail_lock_perms): Tracked<Map<PageIndex, LockPerm>>, Tracked(pcid_allocator_tail_lock_perms): Tracked<Map<PageIndex, LockPerm>>,
    Tracked(container_page_lock_perm): Tracked<LockPerm>, Tracked(pcid_allocator_page_lock_perm): Tracked<LockPerm>,
    Tracked(allocator_4k_page_lock_perm): Tracked<LockPerm>, Tracked(allocator_2m_page_lock_perm): Tracked<LockPerm>,
    Tracked(allocator_1g_page_lock_perm): Tracked<LockPerm>, Tracked(scheduler_page_lock_perm): Tracked<LockPerm>,
    Tracked(cpu_set_page_lock_perm): Tracked<LockPerm>, Tracked(process_page_lock_perm): Tracked<LockPerm>,
    Tracked(pagetable_page_lock_perm): Tracked<LockPerm>, Tracked(l4_page_lock_perm): Tracked<LockPerm>, Tracked(thread_page_lock_perm): Tracked<LockPerm>,
    Tracked(child_container_lock_perm): Tracked<LockPerm>, Tracked(child_process_lock_perm): Tracked<LockPerm>,
    Tracked(child_pagetable_lock_perm): Tracked<LockPerm>, Tracked(child_pcid_allocator_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Ghost<KernelK>))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        pages_4k.wf(),
        pages_4k.len() == 9,
        pages_4k.view().no_duplicates(),
        page_ptr_valid(pages_4k.view().spec_index(0)),
        page_ptr_valid(pages_4k.view().spec_index(1)),
        page_ptr_valid(pages_4k.view().spec_index(2)),
        page_ptr_valid(pages_4k.view().spec_index(3)),
        page_ptr_valid(pages_4k.view().spec_index(4)),
        page_ptr_valid(pages_4k.view().spec_index(5)),
        page_ptr_valid(pages_4k.view().spec_index(6)),
        page_ptr_valid(pages_4k.view().spec_index(7)),
        page_ptr_valid(pages_4k.view().spec_index(8)),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        pages_4k.view().to_set().disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        pages_4k.view().to_set().disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_tail_indices(page_ptr2page_index(container_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(pages_4k.view().spec_index(0)),
            page_ptr2page_index(pages_4k.view().spec_index(1)), page_ptr2page_index(pages_4k.view().spec_index(2)),
            page_ptr2page_index(pages_4k.view().spec_index(3)), page_ptr2page_index(pages_4k.view().spec_index(4)),
            page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)),
            page_ptr2page_index(pages_4k.view().spec_index(7)), page_ptr2page_index(pages_4k.view().spec_index(8)),
        ]),
        page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(pages_4k.view().spec_index(0)),
            page_ptr2page_index(pages_4k.view().spec_index(1)), page_ptr2page_index(pages_4k.view().spec_index(2)),
            page_ptr2page_index(pages_4k.view().spec_index(3)), page_ptr2page_index(pages_4k.view().spec_index(4)),
            page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)),
            page_ptr2page_index(pages_4k.view().spec_index(7)), page_ptr2page_index(pages_4k.view().spec_index(8)),
        ]),
        old(lctx).page_lock_map().dom() == page_ptrs_to_indices(pages_4k.view()).union(seq![page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page)].to_set())
            .union(page_ptrs_to_indices(funding_pages)).union(page_2m_tail_indices(page_ptr2page_index(container_page))).union(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))),
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        funding_pages.to_set().disjoint(pages_4k.view().to_set()),
        page_ptrs_to_indices(funding_pages).disjoint(page_2m_tail_indices(page_ptr2page_index(container_page))),
        page_ptrs_to_indices(funding_pages).disjoint(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))),
        funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page, pcid_allocator_page, pages_4k.view().spec_index(0), pages_4k.view().spec_index(1),
            pages_4k.view().spec_index(2), pages_4k.view().spec_index(3), pages_4k.view().spec_index(8),
            pages_4k.view().spec_index(4), pages_4k.view().spec_index(5), pages_4k.view().spec_index(6),
        )),
        old(krnl).allc_4k_mp.dom().contains(pages_4k.view().spec_index(0)),
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(pages_4k.view().spec_index(0)), state: FreePageAllocatorState::GlobalList })
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_page
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).state() is WriteLock
                &&& funding_page_lock_perms.spec_index(page_ptr).thread_id() == old(lctx).thread_id()
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(container_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(container_page)),
        owned_2m_tail_lock_perms_wf(pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(pcid_allocator_page)),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        progress_peer_of(progress) is None,
        old(krnl).ctn_mp.dom().contains(container_page),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        child_container_lock_perm.state() is WriteLock,
        child_container_lock_perm.thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_page).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(pages_4k.view().spec_index(4)),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), pages_4k.view().spec_index(4), TypedLockMode::Write),
        child_process_lock_perm.state() is WriteLock,
        child_process_lock_perm.thread_id() == old(lctx).thread_id(),
        child_process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4)).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pages_4k.view().spec_index(5)),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pages_4k.view().spec_index(5), TypedLockMode::Write),
        child_pagetable_lock_perm.state() is WriteLock,
        child_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        child_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pages_4k.view().spec_index(5)).locking_thread()->Write_lock_id,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_page, TypedLockMode::Write),
        child_pcid_allocator_lock_perm.state() is WriteLock,
        child_pcid_allocator_lock_perm.thread_id() == old(lctx).thread_id(),
        child_pcid_allocator_lock_perm.lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_page).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(0)), TypedLockMode::Write),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_4k_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(0))).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(1)), TypedLockMode::Write),
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_2m_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(1))).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(2)), TypedLockMode::Write),
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_1g_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(2))).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(3)), TypedLockMode::Write),
        scheduler_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(3))).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(8)), TypedLockMode::Write),
        cpu_set_page_lock_perm.state() is WriteLock,
        cpu_set_page_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(8))).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(4)), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(4))).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(5)), TypedLockMode::Write),
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(5))).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(6)), TypedLockMode::Write),
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(6))).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(7)), TypedLockMode::Write),
        thread_page_lock_perm.state() is WriteLock,
        thread_page_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))).view().locking_thread()->Write_lock_id,
    ensures
        ret.4@ == (KernelK { pg_arr: ret.4@.pg_arr, thr_mp: ret.4@.thr_mp, ..*old(krnl) }),
        ret.4@.inv(),
        ret.4@.thr_mp.unchanged_except(&old(krnl).thr_mp, current_thread_ptr),
        ret.4@.thr_mp.spec_index(current_thread_ptr).view() == (Thread { syscall_progress: Ghost(progress), ..old(krnl).thr_mp.spec_index(current_thread_ptr).view() }),
        ret.4@.thr_mp.spec_index(current_thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread(),
        ret.4@.thr_mp.spec_index(current_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        ret.4@.thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(ret.4@),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, pcid_allc_mp: final(krnl).pcid_allc_mp, ..ret.4@ }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))) == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))),
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(pages_4k.view().spec_index(7))],
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(7)), TypedLockMode::Write),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().remove(pcid_allocator_page),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map().dom() == old(lctx).iommu_table_lock_map().dom(),
        final(lctx).iommu_root_table_lock_map().dom() == old(lctx).iommu_root_table_lock_map().dom(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
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
        ret.3.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))).view().locking_thread()->Write_lock_id,
{
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
    let (container_head, pcid_allocator_head) = new_container_publish_staging_heads(pages_4k, container_page, pcid_allocator_page, Ghost(funding_pages), Ghost(lctx.page_lock_map().dom()));
    cleanup_published_4k_page_chain(krnl, funding_page_count, funding_page_head, Ghost(funding_pages), allocator_4k_page, container_page, Tracked(&mut *lctx), Tracked(funding_page_lock_perms));
    proof {
        assert_sets_equal!(
            lctx.page_lock_map().dom().difference(page_2m_tail_indices(container_head).union(page_2m_tail_indices(pcid_allocator_head)).union(set![
                page_ptr2page_index(allocator_4k_page), page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page),
                page_ptr2page_index(scheduler_page), page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page),
                page_ptr2page_index(pagetable_page), page_ptr2page_index(l4_page), container_head, pcid_allocator_head,
            ])) == set![page_ptr2page_index(thread_page)],
            page_index => {}
        );
    }
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(progress), Tracked(&*lctx), Tracked(current_thread_lock_perm));
    let ghost progressed_k = *krnl;
    let (Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(thread_page_lock_perm)) = finish_staged_container_publish(
        krnl, Tracked(&mut *lctx), pages_4k, container_page, pcid_allocator_page, Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
        Tracked(container_page_lock_perm), Tracked(pcid_allocator_page_lock_perm), Tracked(allocator_4k_page_lock_perm), Tracked(allocator_2m_page_lock_perm),
        Tracked(allocator_1g_page_lock_perm), Tracked(scheduler_page_lock_perm), Tracked(cpu_set_page_lock_perm), Tracked(process_page_lock_perm),
        Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(thread_page_lock_perm), Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(child_pcid_allocator_lock_perm),
    );
    (Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(thread_page_lock_perm), Ghost(progressed_k))
}
} // verus!
