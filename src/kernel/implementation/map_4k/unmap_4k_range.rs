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
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
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
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        old(steps).nonlock_view().len() + range.len <= final(steps).nonlock_view().len(),
        final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 1,
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        final(krnl).irt.owners() == final(steps).snapshot_k().irt.owners(),
        final(krnl).irt.iommu_roots() == final(steps).snapshot_k().irt.iommu_roots(),
        final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
        final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
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
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }

    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    assert(krnl.thr_mp.spec_index(thread_ptr).inv()) by { reveal(thread_perms_wf); };
    let start = range.start;
    let mut i = 0usize;
    while i < range.len
        invariant
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            lctx.page_lock_map().dom().is_empty(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_MAJOR),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.owners() == steps.snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == steps.snapshot_k().irt.iommu_roots(),
            krnl.cpu_tlb.view() == steps.snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
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
            steps.nonlock_view().len() == old(steps).nonlock_view().len() + i,
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
            let process_ptr = krnl.pt_mp.spec_index(pagetable).view().proc_ptr;
            assert(kernel_process_4k_mapping_changed(&steps.snapshot_k(), &*krnl, process_ptr, pagetable, va)) by { reveal(kernel_process_4k_mapping_changed); reveal(process_pagetable_match); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); };
            assert(krnl.prc_mp.dom().contains(process_ptr)
                && !krnl.prc_mp.spec_index(process_ptr).view().zombie
                && krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable) by { reveal(process_pagetable_match); };
            krnl.kernel_step_boundary_process_4k_mapping_changed(
                &mut *lctx, &mut *steps, process_ptr, pagetable, va, process_ptr, pagetable, thread_ptr,
            );
        }
        i = i + 1;
    }
    proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
    proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
    proof { assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; }; }
    flush_pagetable_tlbs(krnl, pagetable, cr3, pcid, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_perm);
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
            lctx.kernel_view_locking_state() is Acquire,
            lctx.page_lock_map().dom().is_empty(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_MAJOR),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.owners() == steps.snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == steps.snapshot_k().irt.iommu_roots(),
            krnl.cpu_tlb.view() == steps.snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
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
            old(steps).nonlock_view().len() + range.len <= steps.nonlock_view().len() <= old(steps).nonlock_view().len() + range.len + NUM_CPUS,
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
        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
        proof { assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; }; }
        reclaim_unmapped_4k_page(krnl, pagetable, va, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm);
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)
                && kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)
                && kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_endpoint_nonlock_fields_unchanged_for_equal;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            };
        }
        i = i + 1;
    }
    proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
    proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
    proof { assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; }; }
    refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm);
    proof {
        assert(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()) by { reveal(thread_perms_wf); };
    }
}
}
