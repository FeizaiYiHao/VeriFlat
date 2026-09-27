use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_transition::ipc_schedule_waiting_peer_and_finish;

verus! {
#[derive(Clone, Copy)]
pub(super) enum IpcPagesMapping {
    Ready,
    SourceUnmapped,
    OwnerMismatch,
    NoQuota,
    Invalid,
    InUse,
}

#[verifier::spinoff_prover]
fn ipc_share_pages_locked(krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr, target_process: RwLockProcessPtr, source_container: RwLockContainerPtr, target_container: RwLockContainerPtr, held_process: RwLockProcessPtr, held_endpoint: RwLockEndpointPtr, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(source_thread_lock_perm): Tracked<&LockPerm>, Tracked(target_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>) -> (ret: IpcPagesMapping)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![source_thread, target_thread],
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(krnl).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
        source_thread != target_thread,
        source_pagetable != target_pagetable,
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().syscall_progress.view() is None,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.state() is WriteLock,
        source_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.state() is WriteLock,
        target_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(held_process),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), held_process, TypedLockMode::Write),
        old(krnl).ep_mp.dom().contains(held_endpoint),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), held_endpoint, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![held_process],
        old(lctx).endpoint_lock_map().dom() =~= set![held_endpoint],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
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
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
    ensures
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
            old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view()) ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), held_process, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), held_endpoint, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).prc_mp.spec_index(held_process) == old(krnl).prc_mp.spec_index(held_process),
        final(krnl).ep_mp.spec_index(held_endpoint) == old(krnl).ep_mp.spec_index(held_endpoint),
        final(krnl).thr_mp.spec_index(source_thread).being_killed() == old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().state == old(krnl).thr_mp.spec_index(source_thread).view().state,
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        final(krnl).thr_mp.spec_index(source_thread).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(source_thread).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().syscall_progress.view() is None,
        final(krnl).thr_mp.spec_index(target_thread).being_killed() == old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(target_thread).view().state == old(krnl).thr_mp.spec_index(target_thread).view().state,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == old(krnl).thr_mp.spec_index(target_thread).view().owning_proc,
        final(krnl).thr_mp.spec_index(target_thread).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(target_thread).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().syscall_progress.view() is None,
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        final(krnl).irt.owners() == final(steps).snapshot_k().irt.owners(),
        final(krnl).irt.iommu_roots() == final(steps).snapshot_k().irt.iommu_roots(),
        final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
        final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        ret is Ready ==> old(steps).nonlock_view().len() + source_range.len <= final(steps).nonlock_view().len()
            <= old(steps).nonlock_view().len() + 4 * source_range.len,
        !(ret is Ready) ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len(),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        final(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(target_thread),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(final(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == final(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
{
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }

    let source_start_indices = va2index(source_range.start);
    proof {
        assert({
            &&& krnl.pt_mp.perms_wf()
            &&& krnl.pt_mp.spec_index(source_pagetable).inv()
            &&& krnl.pt_mp.spec_index(target_pagetable).inv()
            &&& krnl.thr_mp.perms_wf()
            &&& krnl.thr_mp.spec_index(target_thread).inv()
        }) by { reveal(pagetable_perms_wf); reveal(thread_perms_wf); };
    }
    let source_pt = krnl.pt_mp.borrow_typed(source_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(source_pagetable_lock_perm));
    if source_start_indices.0 < source_pt.kernel_l4_end {
        return IpcPagesMapping::Invalid;
    }
    if !share_mapping_4k_source_precheck(krnl, source_range, source_pagetable, Tracked(&*lctx), Tracked(source_pagetable_lock_perm)) {
        return IpcPagesMapping::SourceUnmapped;
    }

    let range_len = target_range.len;
    let target_thread_ref = krnl.thr_mp.borrow_typed(target_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(target_thread_lock_perm));
    if target_thread_ref.quota_4k < 3usize * range_len {
        return IpcPagesMapping::NoQuota;
    }
    let target_start = target_range.start;
    let target_start_indices = va2index(target_start);
    let target_pt = krnl.pt_mp.borrow_typed(target_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(target_pagetable_lock_perm));
    if target_start_indices.0 < target_pt.kernel_l4_end {
        return IpcPagesMapping::Invalid;
    }
    let target_end_index = range_len - 1;
    let target_end = target_range.index(target_end_index);
    proof {
        assert(target_end == spec_va_add_range(target_start, target_end_index)) by { target_range.va_range_lemma(); };
        assert(target_start <= target_end) by { target_range.va_range_lemma(); };
    }
    if !target_pt.mapping_4k_va_range_empty(target_start, target_end) {
        return IpcPagesMapping::InUse;
    }
    if !target_pt.mapping_4k_va_range_buildable(target_range) {
        return IpcPagesMapping::InUse;
    }

    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(source_container)
            &&& krnl.ctn_mp.dom().contains(target_container)
            &&& container_perms_wf(krnl.ctn_mp)
            &&& container_tree_wf(krnl.rt_ctn, krnl.ctn_mp)
        }) by { reveal(container_thread_wf); };
    }
    let containers_compatible = if source_container == target_container {
        true
    } else {
        container_tree_check_is_ancestor(krnl.rt_ctn, &krnl.ctn_mp, source_container, target_container)
    };
    let owners_compatible = if containers_compatible {
        proof {
            assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range)) by {
                source_range.va_range_lemma();
                reveal(mapped_4k_page_pagetable_wf); reveal(container_process_page_pagetable_wf); reveal(container_page_owner_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(process_pagetable_match); reveal(container_perms_wf); reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_subtree_set_exclusive);
            };
        }
        true
    } else {
        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        share_mapping_4k_source_owner_precheck(krnl, source_range, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(target_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm))
    };
    proof {
        assert({
            &&& held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx))
            &&& held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx))
            &&& held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx))
        }) by { broadcast use group_held_objects_unchanged_transitive; };
    }
    if !owners_compatible {
        return IpcPagesMapping::OwnerMismatch;
    }

    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(target_container)
            &&& krnl.ctn_mp.view().spec_index(target_container).is_init()
            &&& krnl.ctn_mp.view().spec_index(target_container).addr() == target_container
        }) by { reveal(container_thread_wf); reveal(container_perms_wf); };
    }
    let target_allocator = krnl.ctn_mp.borrow_rodata(target_container).borrow().allocator_ptr_4k;
    proof {
        assert(krnl.allc_4k_mp.dom().contains(target_allocator)) by { reveal(container_allocator_wf); };
    }
    proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    proof { assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; }; }
    share_mapping_4k_build_and_share(
        krnl, source_range, target_range, target_allocator, source_thread, target_thread, target_process, target_container, cpu_id,
        source_pagetable, target_pagetable, None, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm),
        Tracked(target_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(None),
        Tracked(None),
    );
    IpcPagesMapping::Ready
}

pub(super) fn ipc_rendezvous_pages(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_lock_perm: Tracked<LockPerm>,
    process_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<LockPerm>,
    peer_thread_lock_perm: Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        current_thread_ptr != peer_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        process_lock_perm.view().state() is WriteLock,
        process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        endpoint_lock_perm.view().state() is WriteLock,
        endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0,
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
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
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_thread != target_thread,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret is Success || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is Error,
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        ret is Success ==> old(steps).nonlock_view().len() + source_range.len + 1 <= final(steps).nonlock_view().len()
            <= old(steps).nonlock_view().len() + 4 * source_range.len + 1,
        !(ret is Success) ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
{
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }

    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked process_lock_perm = process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();

    proof {
        assert({
            &&& krnl.thr_mp.perms_wf()
            &&& krnl.thr_mp.spec_index(current_thread_ptr).is_init()
            &&& krnl.thr_mp.spec_index(peer_thread_ptr).is_init()
        }) by { reveal(thread_perms_wf); };
    }
    let source_process;
    let source_container;
    let source_pagetable;
    if source_thread == current_thread_ptr {
        let source_thread_ref = krnl.thr_mp.borrow_typed(source_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
        source_process = source_thread_ref.owning_proc;
        source_container = source_thread_ref.owning_container;
        source_pagetable = source_thread_ref.proc_pagetable_ptr;
    } else {
        let source_thread_ref = krnl.thr_mp.borrow_typed(source_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
        source_process = source_thread_ref.owning_proc;
        source_container = source_thread_ref.owning_container;
        source_pagetable = source_thread_ref.proc_pagetable_ptr;
    }
    let target_process;
    let target_container;
    let target_pagetable;
    if target_thread == current_thread_ptr {
        let target_thread_ref = krnl.thr_mp.borrow_typed(target_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
        target_process = target_thread_ref.owning_proc;
        target_container = target_thread_ref.owning_container;
        target_pagetable = target_thread_ref.proc_pagetable_ptr;
    } else {
        let target_thread_ref = krnl.thr_mp.borrow_typed(target_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
        target_process = target_thread_ref.owning_proc;
        target_container = target_thread_ref.owning_container;
        target_pagetable = target_thread_ref.proc_pagetable_ptr;
    }

    if source_process == target_process {
        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        return ipc_schedule_waiting_peer_and_finish(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, Ghost(None), peer_thread_ptr,
            RetValueType::ErrorIpcSameProcess, Tracked(cpu_lock_perm), Tracked(process_lock_perm),
            Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
        );
    } else {
        proof {
            assert({
                &&& krnl.prc_mp.dom().contains(source_process)
                &&& krnl.prc_mp.dom().contains(target_process)
                &&& krnl.pt_mp.dom().contains(source_pagetable)
                &&& krnl.pt_mp.dom().contains(target_pagetable)
                &&& krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process
                &&& krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process
                &&& source_pagetable != target_pagetable
            }) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
        }

        let (Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm)) = krnl.wlock_pagetable_pair(source_pagetable, target_pagetable, Tracked(&mut *lctx));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.rebase_snapshot_k_if_unchanged(&*krnl);

            assert({
                &&& krnl.thr_mp.dom().contains(source_thread)
                &&& krnl.thr_mp.dom().contains(target_thread)
                &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), source_thread, TypedLockMode::Write)
                &&& !krnl.thr_mp.spec_index(source_thread).being_killed()
                &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), target_thread, TypedLockMode::Write)
                &&& !krnl.thr_mp.spec_index(target_thread).being_killed()
                &&& krnl.thr_mp.spec_index(source_thread).view().owning_proc != target_process
                &&& krnl.thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable
                &&& krnl.thr_mp.spec_index(target_thread).view().owning_container == target_container
            }) by { reveal(process_thread_wf); };
            assert({
                &&& krnl.prc_mp.dom().contains(target_process)
                &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container
                &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable
                &&& {
                    ||| {
                        &&& krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process
                        &&& krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable
                    }
                    ||| typed_lock_map_contains_mode(lctx.process_lock_map(), target_process, TypedLockMode::Write)
                }
                &&& krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == krnl.thr_mp.spec_index(source_thread).view().owning_proc
                &&& krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process
            }) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
            assert({
                &&& krnl.pt_mp.dom().contains(source_pagetable)
                &&& krnl.pt_mp.dom().contains(target_pagetable)
                &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Write)
                &&& krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == krnl.thr_mp.spec_index(source_thread).view().owning_proc
                &&& krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process
                &&& (&source_pagetable_lock_perm).state() is WriteLock
                &&& (&source_pagetable_lock_perm).thread_id() == lctx.thread_id()
                &&& (&source_pagetable_lock_perm).lock_id() == krnl.pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id
                &&& (&target_pagetable_lock_perm).state() is WriteLock
                &&& (&target_pagetable_lock_perm).thread_id() == lctx.thread_id()
                &&& (&target_pagetable_lock_perm).lock_id() == krnl.pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id
            }) by { reveal(process_pagetable_match); };
        }
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        }
        let pages_result = ipc_share_pages_locked(
            krnl, source_range, target_range, source_thread, target_thread, target_process,
            source_container, target_container, process_ptr, endpoint_ptr,
            source_pagetable, target_pagetable, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps),
            Tracked(if source_thread == current_thread_ptr { &current_thread_lock_perm } else { &peer_thread_lock_perm }),
            Tracked(if target_thread == current_thread_ptr { &current_thread_lock_perm } else { &peer_thread_lock_perm }),
            Tracked(&source_pagetable_lock_perm), Tracked(&target_pagetable_lock_perm),
        );
        if source_pagetable < target_pagetable {
            krnl.wunlock_pagetable(target_pagetable, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
            krnl.wunlock_pagetable(source_pagetable, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        } else {
            krnl.wunlock_pagetable(source_pagetable, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
            krnl.wunlock_pagetable(target_pagetable, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
        }
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
                reveal(kernel_pagetable_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
        let result = match pages_result {
            IpcPagesMapping::Ready => RetValueType::Success,
            IpcPagesMapping::SourceUnmapped => RetValueType::ErrorIpcSourceUnmapped,
            IpcPagesMapping::OwnerMismatch => RetValueType::ErrorIpcPageOwnerMismatch,
            IpcPagesMapping::NoQuota => RetValueType::ErrorNoQuota,
            IpcPagesMapping::InUse => RetValueType::ErrorVaInUse,
            _ => RetValueType::Error,
        };
        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        proof { assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; }; }
        return ipc_schedule_waiting_peer_and_finish(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, Ghost(None), peer_thread_ptr,
            result, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm),
            Tracked(peer_thread_lock_perm),
        );
    }
}
} // verus!
