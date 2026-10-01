use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) fn finish_staged_container_publish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, pages_4k: &ArrayVec<PagePtr, 9>, container_page: PagePtr,
    pcid_allocator_page: PagePtr, Tracked(container_tail_lock_perms): Tracked<Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<Map<PageIndex, LockPerm>>, Tracked(container_page_lock_perm): Tracked<LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<LockPerm>, Tracked(allocator_4k_page_lock_perm): Tracked<LockPerm>,
    Tracked(allocator_2m_page_lock_perm): Tracked<LockPerm>, Tracked(allocator_1g_page_lock_perm): Tracked<LockPerm>,
    Tracked(scheduler_page_lock_perm): Tracked<LockPerm>, Tracked(cpu_set_page_lock_perm): Tracked<LockPerm>,
    Tracked(process_page_lock_perm): Tracked<LockPerm>, Tracked(pagetable_page_lock_perm): Tracked<LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<LockPerm>, Tracked(thread_page_lock_perm): Tracked<LockPerm>,
    Tracked(child_container_lock_perm): Tracked<LockPerm>, Tracked(child_process_lock_perm): Tracked<LockPerm>,
    Tracked(child_pagetable_lock_perm): Tracked<LockPerm>, Tracked(child_scheduler_lock_perm): Tracked<LockPerm>,
    Tracked(child_pcid_allocator_lock_perm): Tracked<LockPerm>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
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
        old(krnl).allc_4k_mp.dom().contains(pages_4k.view().spec_index(0)),
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
        old(lctx).page_lock_map().dom().difference(page_2m_tail_indices(page_ptr2page_index(container_page)).union(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))).union(seq![
            page_ptr2page_index(pages_4k.view().spec_index(0)), page_ptr2page_index(pages_4k.view().spec_index(1)),
            page_ptr2page_index(pages_4k.view().spec_index(2)), page_ptr2page_index(pages_4k.view().spec_index(3)),
            page_ptr2page_index(pages_4k.view().spec_index(8)), page_ptr2page_index(pages_4k.view().spec_index(4)),
            page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)),
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page),
        ].to_set())) =~= set![page_ptr2page_index(pages_4k.view().spec_index(7))],
        owned_2m_tail_lock_perms_wf(container_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(container_page)),
        owned_2m_tail_lock_perms_wf(pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(pcid_allocator_page)),
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
        old(krnl).sched_mp.dom().contains(pages_4k.view().spec_index(3)),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), pages_4k.view().spec_index(3), TypedLockMode::Write),
        child_scheduler_lock_perm.state() is WriteLock,
        child_scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        child_scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(pages_4k.view().spec_index(3)).locking_thread()->Write_lock_id,
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
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(pages_4k.view().spec_index(7))],
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map().dom() == old(lctx).endpoint_lock_map().dom(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().remove(pcid_allocator_page),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map().dom() == old(lctx).iommu_table_lock_map().dom(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(krnl).allc_4k_mp.dom().contains(pages_4k.view().spec_index(0)),
        final(krnl).allc_4k_mp.spec_index(pages_4k.view().spec_index(0)) == old(krnl).allc_4k_mp.spec_index(pages_4k.view().spec_index(0)),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, pcid_allc_mp: final(krnl).pcid_allc_mp, ..*old(krnl) }),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), pages_4k.view().spec_index(4), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pages_4k.view().spec_index(5), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), pages_4k.view().spec_index(3), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(7)), TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))) == old(krnl).pg_arr.spec_index(page_ptr2page_index(pages_4k.view().spec_index(7))),
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
    let allocator_4k_page = *pages_4k.get(0);
    let allocator_2m_page = *pages_4k.get(1);
    let allocator_1g_page = *pages_4k.get(2);
    let scheduler_page = *pages_4k.get(3);
    let cpu_set_page = *pages_4k.get(8);
    let process_page = *pages_4k.get(4);
    let pagetable_page = *pages_4k.get(5);
    let l4_page = *pages_4k.get(6);
    let thread_page = *pages_4k.get(7);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);

    wunlock_owned_2m_page_tails(krnl, container_head, Tracked(&mut *lctx), Tracked(container_tail_lock_perms));
    wunlock_owned_2m_page_tails(krnl, pcid_allocator_head, Tracked(&mut *lctx), Tracked(pcid_allocator_tail_lock_perms));
    assert({
        &&& seq![
            page_ptr2page_index(allocator_4k_page), page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page),
            page_ptr2page_index(scheduler_page), page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page),
            page_ptr2page_index(pagetable_page), page_ptr2page_index(l4_page), container_head,
            pcid_allocator_head,
        ].no_duplicates()
        &&& !set![
            page_ptr2page_index(allocator_4k_page), page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page),
            page_ptr2page_index(scheduler_page), page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page),
            page_ptr2page_index(pagetable_page), page_ptr2page_index(l4_page), container_head,
            pcid_allocator_head,
        ].contains(page_ptr2page_index(thread_page))
    }) by { page_ptr_roundtrip(); page_ptr2page_index_injective(); page_2m_all_ptrs_contains_head(container_head); page_2m_all_ptrs_contains_head(pcid_allocator_head); };
    release_container_backing_page_locks(
        &mut krnl.pg_arr, Tracked(&mut *lctx),
        (page_ptr2page_index(allocator_4k_page), page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page),
            page_ptr2page_index(scheduler_page), page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page),
            page_ptr2page_index(pagetable_page), page_ptr2page_index(l4_page), container_head, pcid_allocator_head),
        Tracked(allocator_4k_page_lock_perm), Tracked(allocator_2m_page_lock_perm),
        Tracked(allocator_1g_page_lock_perm), Tracked(scheduler_page_lock_perm),
        Tracked(cpu_set_page_lock_perm), Tracked(process_page_lock_perm),
        Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm),
        Tracked(container_page_lock_perm), Tracked(pcid_allocator_page_lock_perm),
    );
    proof {
        assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
        assert(krnl.memory_management_inv()) by { memory_management_inv_preserved_for_page_invariant_fields(*old(krnl), *krnl); };
        assert(kernel_k_to_nonlock_kernel_u(*krnl) == kernel_k_to_nonlock_kernel_u(*old(krnl))) by {
            reveal(kernel_endpoint_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(old(krnl), krnl);
        };
    }
    krnl.wunlock_pcid_allocator(pcid_allocator_page, Tracked(&mut *lctx), Tracked(child_pcid_allocator_lock_perm));
    proof {
        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
            reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
        };
    }

    (Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm),
        Tracked(child_scheduler_lock_perm), Tracked(thread_page_lock_perm))
}

#[verifier::spinoff_prover]
fn release_container_backing_page_locks(
    pages: &mut PageLockedArray, Tracked(lctx): Tracked<&mut LocalContext>,
    indices: (PageIndex, PageIndex, PageIndex, PageIndex, PageIndex, PageIndex, PageIndex, PageIndex, PageIndex, PageIndex),
    Tracked(perm0): Tracked<LockPerm>, Tracked(perm1): Tracked<LockPerm>, Tracked(perm2): Tracked<LockPerm>, Tracked(perm3): Tracked<LockPerm>,
    Tracked(perm4): Tracked<LockPerm>, Tracked(perm5): Tracked<LockPerm>, Tracked(perm6): Tracked<LockPerm>, Tracked(perm7): Tracked<LockPerm>,
    Tracked(perm8): Tracked<LockPerm>, Tracked(perm9): Tracked<LockPerm>,
)
    requires
        page_array_wf(*old(pages)),
        old(pages).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Release,
        seq![indices.0, indices.1, indices.2, indices.3, indices.4, indices.5, indices.6, indices.7, indices.8, indices.9].no_duplicates(),
        index_valid(NUM_PAGES, indices.0),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.0, TypedLockMode::Write),
        perm0.state() is WriteLock,
        perm0.thread_id() == old(lctx).thread_id(),
        perm0.lock_id() == old(pages).spec_index(indices.0).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.1),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.1, TypedLockMode::Write),
        perm1.state() is WriteLock,
        perm1.thread_id() == old(lctx).thread_id(),
        perm1.lock_id() == old(pages).spec_index(indices.1).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.2),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.2, TypedLockMode::Write),
        perm2.state() is WriteLock,
        perm2.thread_id() == old(lctx).thread_id(),
        perm2.lock_id() == old(pages).spec_index(indices.2).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.3),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.3, TypedLockMode::Write),
        perm3.state() is WriteLock,
        perm3.thread_id() == old(lctx).thread_id(),
        perm3.lock_id() == old(pages).spec_index(indices.3).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.4),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.4, TypedLockMode::Write),
        perm4.state() is WriteLock,
        perm4.thread_id() == old(lctx).thread_id(),
        perm4.lock_id() == old(pages).spec_index(indices.4).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.5),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.5, TypedLockMode::Write),
        perm5.state() is WriteLock,
        perm5.thread_id() == old(lctx).thread_id(),
        perm5.lock_id() == old(pages).spec_index(indices.5).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.6),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.6, TypedLockMode::Write),
        perm6.state() is WriteLock,
        perm6.thread_id() == old(lctx).thread_id(),
        perm6.lock_id() == old(pages).spec_index(indices.6).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.7),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.7, TypedLockMode::Write),
        perm7.state() is WriteLock,
        perm7.thread_id() == old(lctx).thread_id(),
        perm7.lock_id() == old(pages).spec_index(indices.7).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.8),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.8, TypedLockMode::Write),
        perm8.state() is WriteLock,
        perm8.thread_id() == old(lctx).thread_id(),
        perm8.lock_id() == old(pages).spec_index(indices.8).view().locking_thread()->Write_lock_id,
        index_valid(NUM_PAGES, indices.9),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), indices.9, TypedLockMode::Write),
        perm9.state() is WriteLock,
        perm9.thread_id() == old(lctx).thread_id(),
        perm9.lock_id() == old(pages).spec_index(indices.9).view().locking_thread()->Write_lock_id,
    ensures
        page_array_wf(*final(pages)),
        page_invariant_fields_unchanged(*old(pages), *final(pages)),
        final(pages).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).page_lock_map() == old(lctx).page_lock_map().remove_keys(set![indices.0, indices.1, indices.2, indices.3, indices.4, indices.5, indices.6, indices.7, indices.8, indices.9]),
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
        forall|index: PageIndex| #![trigger final(pages).spec_index(index)] index_valid(NUM_PAGES, index) && !set![
            indices.0, indices.1, indices.2, indices.3, indices.4, indices.5, indices.6, indices.7, indices.8, indices.9,
        ].contains(index) ==> final(pages).spec_index(index) == old(pages).spec_index(index),
{
    assert(pages.inv()) by { reveal(page_array_wf); };
    assert({
        &&& pages.spec_index(indices.0).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.0), KernelObjId::Page(indices.0))
        &&& pages.spec_index(indices.1).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.1), KernelObjId::Page(indices.1))
        &&& pages.spec_index(indices.2).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.2), KernelObjId::Page(indices.2))
        &&& pages.spec_index(indices.3).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.3), KernelObjId::Page(indices.3))
        &&& pages.spec_index(indices.4).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.4), KernelObjId::Page(indices.4))
        &&& pages.spec_index(indices.5).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.5), KernelObjId::Page(indices.5))
        &&& pages.spec_index(indices.6).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.6), KernelObjId::Page(indices.6))
        &&& pages.spec_index(indices.7).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.7), KernelObjId::Page(indices.7))
        &&& pages.spec_index(indices.8).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.8), KernelObjId::Page(indices.8))
        &&& pages.spec_index(indices.9).view().wlocked_by(&*lctx)
        &&& lctx.lock_entry_contains(pages.lock_id_by_index(indices.9), KernelObjId::Page(indices.9))
    }) by { reveal(LockedArray::typed_lock_map_aligned); };
    pages.wunlock(indices.0, Tracked(&mut *lctx), Tracked(perm0), Ghost(KernelObjId::Page(indices.0)));
    pages.wunlock(indices.1, Tracked(&mut *lctx), Tracked(perm1), Ghost(KernelObjId::Page(indices.1)));
    pages.wunlock(indices.2, Tracked(&mut *lctx), Tracked(perm2), Ghost(KernelObjId::Page(indices.2)));
    pages.wunlock(indices.3, Tracked(&mut *lctx), Tracked(perm3), Ghost(KernelObjId::Page(indices.3)));
    pages.wunlock(indices.4, Tracked(&mut *lctx), Tracked(perm4), Ghost(KernelObjId::Page(indices.4)));
    pages.wunlock(indices.5, Tracked(&mut *lctx), Tracked(perm5), Ghost(KernelObjId::Page(indices.5)));
    pages.wunlock(indices.6, Tracked(&mut *lctx), Tracked(perm6), Ghost(KernelObjId::Page(indices.6)));
    pages.wunlock(indices.7, Tracked(&mut *lctx), Tracked(perm7), Ghost(KernelObjId::Page(indices.7)));
    pages.wunlock(indices.8, Tracked(&mut *lctx), Tracked(perm8), Ghost(KernelObjId::Page(indices.8)));
    pages.wunlock(indices.9, Tracked(&mut *lctx), Tracked(perm9), Ghost(KernelObjId::Page(indices.9)));
    assert(page_array_wf(*pages)) by { reveal(page_array_wf); };
    assert(pages.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
}
}
