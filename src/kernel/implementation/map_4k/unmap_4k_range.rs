use vstd::prelude::*;
use crate::*;
use super::unmap_4k_present::clear_4k_mapping_present;
use super::unmap_4k_flush_all::flush_pagetable_tlbs;
use super::unmap_4k_reclaim_one::reclaim_unmapped_4k_page;

verus! {
pub fn unmap_4k_range(krnl: &mut KernelK, range: &VaRange4K, pagetable: RwLockPageTableRoot, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>, pagetable_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_id() == cpu_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_perm.view().state() is WriteLock,
        cpu_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_published[cpu_id as int].view() == (cr3, pcid),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        range.wf(),
        range.len > 0,
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(range.start).0,
        share_mapping_4k_source_range_present(old(krnl), pagetable, range),
    ensures
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(steps).steps.len() == old(steps).steps.len() + range.len,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == old(krnl).thr_mp.spec_index(thread_ptr).view(),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().remove_keys(range.view().to_set()),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g(),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pagetable, final(krnl).pt_mp.spec_index(pagetable).view()),
{
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    assert(krnl.thr_mp.spec_index(thread_ptr).inv()) by { reveal(thread_perms_wf); };
    let start = range.start;
    let mut i = 0usize;
    while i < range.len
        invariant
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lock_id_set_aligned(lctx),
            lctx.kernel_view_locking_state() is Acquire,
            lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
            lctx.page_lock_map().dom().is_empty(),
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            index_valid(NUM_CPUS, cpu_id),
            lctx.cpu_id() == cpu_id,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_perm.view().state() is WriteLock,
            cpu_perm.view().thread_id() == lctx.thread_id(),
            cpu_perm.view().lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
            krnl.cpu_published[cpu_id as int].view() == (cr3, pcid),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            krnl.thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == lctx.thread_id(),
            thread_perm.view().lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
            krnl.pt_mp.dom().contains(pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == lctx.thread_id(),
            pagetable_perm.view().lock_id() == krnl.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3,
            krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            range.wf(),
            range.len > 0,
            start == range.start,
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(range.start).0,
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            krnl.cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_4k().remove_keys(range.view().to_set()) == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().remove_keys(range.view().to_set()),
            i <= range.len,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).inv(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).pt_mp.dom().contains(pagetable),
            krnl.thr_mp.spec_index(thread_ptr).view() == old(krnl).thr_mp.spec_index(thread_ptr).view(),
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            steps.steps.len() == old(steps).steps.len() + i,
            krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom(),
            forall|j: int| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j))] #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(range.view().spec_index(j))] 0 <= j < range.len ==> { &&& krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j)) &&& krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(range.view().spec_index(j)).present == (i <= j) },
        decreases range.len - i,
    {
        let va = range.index(i);
        proof {
            assert(va_4k_valid(va) && range.start <= va && spec_va_4k_valid(range.start) && spec_va_4k_valid(va)) by { range.va_range_lemma(); };
            assert(krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0) by {
                spec_v2l4index_monotonic(start, va);
            };
        }
        clear_4k_mapping_present(krnl, pagetable, va, Tracked(&mut *lctx), pagetable_perm);
        proof {
            assert(lctx.holds_no_allocator_locks(PageSize::SZ4k)) by { reveal(LocalContext::holds_no_allocator_locks); };
            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
        }
        i = i + 1;
    }
    flush_pagetable_tlbs(krnl, pagetable, cr3, pcid, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_perm);
    assert(lctx.holds_no_allocator_locks(PageSize::SZ4k) && lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)) by { reveal(LocalContext::holds_no_allocator_locks); broadcast use held_lock_major_lt_preserved_for_typed_maps_unchanged; };
    assert(krnl.thr_mp.spec_index(thread_ptr).inv()) by { reveal(thread_perms_wf); };
    assert(krnl.thr_mp.spec_index(thread_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH) by { reveal(container_thread_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    i = 0;
    while i < range.len
        invariant
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lock_id_set_aligned(lctx),
            lctx.kernel_view_locking_state() is Acquire,
            lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
            lctx.page_lock_map().dom().is_empty(),
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            index_valid(NUM_CPUS, cpu_id),
            lctx.cpu_id() == cpu_id,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_perm.view().state() is WriteLock,
            cpu_perm.view().thread_id() == lctx.thread_id(),
            cpu_perm.view().lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            krnl.thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == lctx.thread_id(),
            thread_perm.view().lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
            krnl.pt_mp.dom().contains(pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == lctx.thread_id(),
            pagetable_perm.view().lock_id() == krnl.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            range.wf(),
            range.len > 0,
            start == range.start,
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(range.start).0,
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            krnl.cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_4k().remove_keys(range.view().to_set()) == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().remove_keys(range.view().to_set()),
            i <= range.len,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).inv(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).pt_mp.dom().contains(pagetable),
            steps.steps.len() == old(steps).steps.len() + range.len,
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
            direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < krnl.thr_mp.spec_index(thread_ptr).view().container_depth ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pagetable, krnl.pt_mp.spec_index(pagetable).view()),
            forall|j: int| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j))] #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(range.view().spec_index(j))] 0 <= j < range.len ==> (if j < i { !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j)) } else { krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j)) && !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(range.view().spec_index(j)).present }),
        decreases range.len - i,
    {
        let va = range.index(i);
        proof {
            assert(va_4k_valid(va) && range.start <= va && spec_va_4k_valid(range.start) && spec_va_4k_valid(va)) by { range.va_range_lemma(); };
            assert(krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0) by {
                spec_v2l4index_monotonic(start, va);
            };
        }
        reclaim_unmapped_4k_page(krnl, pagetable, va, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm);
        i = i + 1;
    }
    refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm);
    proof {
        assert(lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)) by { broadcast use held_lock_major_lt_preserved_for_typed_maps_unchanged; };
        assert(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()) by { reveal(thread_perms_wf); };
    }
}
}
