use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
use super::super::syscall_new_process_publish::publish_staged_process;
use super::super::syscall_new_process_spec::*;
use super::super::syscall_new_process_trace::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(in super::super) fn commit_new_process(
    krnl: &mut KernelK, source_range: &VaRange4K, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    container_ptr: RwLockContainerPtr, parent_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, source_pagetable_ptr: RwLockPageTableRoot,
    endpoint: Option<RwLockEndpointPtr>, endpoint_index: EndpointIdx, pcid: Pcid, cpu_lock_perm: Tracked<LockPerm>,
    pcid_allocator_lock_perm: Tracked<LockPerm>, parent_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>, source_pagetable_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<Option<LockPerm>>,
    initial_regs: &Registers,
) -> (ret: (RwLockProcessPtr, RwLockThreadPtr))
    requires *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp,
            thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, pt_mp: old(krnl).pt_mp, pcid_allc_mp: old(krnl).pcid_allc_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, parent_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, current_thread_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, source_pagetable_ptr),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(steps).snapshot_k().prc_mp.spec_index(parent_ptr).locking_thread() is None,
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).locking_thread() is None,
        old(steps).snapshot_k().pt_mp.spec_index(source_pagetable_ptr).locking_thread() is None,
        endpoint is Some ==> old(steps).snapshot_k().ep_mp.spec_index(endpoint->Some_0).locking_thread() is None,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        match endpoint { Some(e) => old(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, e), None => old(krnl).ep_mp == old(steps).snapshot_k().ep_mp },
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        source_range.wf(),
        source_range.len > 0,
        source_range.len <= (usize::MAX - 4) / 3,
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        pcid_allocator_lock_perm.view().state() is WriteLock,
        pcid_allocator_lock_perm.view().thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.view().lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        parent_lock_perm.view().state() is WriteLock,
        parent_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 4 + 3 * source_range.len,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().leaves_present(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().wf(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        source_pagetable_lock_perm.view().state() is WriteLock,
        source_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        share_mapping_4k_source_range_present(old(krnl), source_pagetable_ptr, source_range),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![parent_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            let endpoint_owner = old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container;
            &&& edp_idx_valid(endpoint_index)
            &&& old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == endpoint
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& !old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
            &&& old(krnl).ctn_mp.dom().contains(endpoint_owner)
            &&& endpoint_owner == container_ptr || old(krnl).ctn_mp.spec_index(endpoint_owner).view_ghost().subtree_set.view().contains(container_ptr)
            &&& endpoint_lock_perm.view() is Some
            &&& endpoint_lock_perm.view()->Some_0.state() is WriteLock
            &&& endpoint_lock_perm.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm.view()->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom() =~= set![pcid_allocator_ptr],
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        old(steps).view().len() as int + source_range.len as int + 3 <= final(steps).view().len() as int <= old(steps).view().len() as int + 4 * source_range.len as int + 3,
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        new_process_commit_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), old(steps).snapshot_u(), cpu_id,
            *source_range, *initial_regs, if endpoint is Some { Some(endpoint_index) } else { None }, false),
        final(steps).view().last().new_u == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        old(steps).nonlock_view().len() as int + source_range.len as int + 3 <= final(steps).nonlock_view().len() as int,
        final(steps).nonlock_view().len() as int <= old(steps).nonlock_view().len() as int + 4 * source_range.len as int + 3,
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_u_new_thread_changed(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, ret.0, current_thread_ptr, container_ptr, ret.1, *initial_regs, endpoint, None),
        final(krnl).thr_mp.dom().contains(ret.1),
        final(krnl).thr_mp.spec_index(ret.1).view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(ret.1).view().owning_proc == ret.0,
        final(krnl).thr_mp.spec_index(ret.1).view().owning_container == container_ptr,
        endpoint is Some ==> final(krnl).thr_mp.spec_index(ret.1).view().endpoint_descriptors.wf(),
        endpoint is Some ==> final(krnl).thr_mp.spec_index(ret.1).view().endpoint_descriptors.spec_index(0) == endpoint,
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked pcid_allocator_lock_perm = pcid_allocator_lock_perm.get();
    let tracked parent_lock_perm = parent_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let ghost endpoint_index_opt: Option<EndpointIdx> = if endpoint is Some { Some(endpoint_index) } else { None };
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(Some(SyscallProgress::NewProcess(NewProcessProgress {
        range: *source_range, regs: *initial_regs, endpoint_index: endpoint_index_opt, with_iommu: false, child: None,
    }))), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
    proof {
        use_type_invariant(&*steps);
        let ghost entered_k = *krnl;
        assert(PcidAllocator::free_pcids(old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().ref_counters.view()).contains(pcid)
            && steps.snapshot_k().thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None) by {
            reveal(process_thread_wf); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, current_thread_ptr);
        assert(new_process_trace_after_enter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), old(steps).snapshot_u(), cpu_id,
            *source_range, *initial_regs, endpoint_index_opt, false)) by {
            reveal(process_thread_wf); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(&old(steps).snapshot_k(), old(krnl), old(lctx),
                cpu_id, parent_ptr, current_thread_ptr, endpoint, true, None, true, None);
            kernel_thread_syscall_progress_changed_implies_u_step(old(krnl), &entered_k, current_thread_ptr);
            kernel_l4_end_projection_at(old(krnl), source_pagetable_ptr);
            kernel_cpu_thread_projection_at(&old(steps).snapshot_k(), cpu_id, parent_ptr, current_thread_ptr, None);
            new_process_enter_step_from_u(old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id, parent_ptr,
                current_thread_ptr, container_ptr, endpoint, *source_range, *initial_regs, endpoint_index_opt, false);
            new_process_trace_enter_step(&*steps, old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(entered_k), cpu_id, *source_range, *initial_regs,
                endpoint_index_opt, false);
        };
        assert(krnl.ctn_mp.dom().contains(container_ptr)) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, current_thread_ptr); };
    }
    let (process_page_ptr, pagetable_page_ptr, l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm)) = allocate_new_process_pages(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), current_thread_ptr, container_ptr, cpu_id, Tracked(&current_thread_lock_perm),
    );
    proof {
        assert(!krnl.prc_mp.dom().contains(process_page_ptr)) by { page_ptr_roundtrip(); reveal(process_pages_wf); };
        assert(!krnl.pt_mp.dom().contains(pagetable_page_ptr)) by { page_ptr_roundtrip(); reveal(pagetable_pages_wf); };
    }
    let ghost publish_before = steps.view();
    let (child_ptr, target_pagetable_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm)) = publish_staged_process(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr, pcid_allocator_ptr,
        source_pagetable_ptr, source_range, pcid, process_page_ptr, pagetable_page_ptr, l4_page_ptr, Tracked(process_page_lock_perm),
        Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(&cpu_lock_perm),
        Tracked(pcid_allocator_lock_perm), Tracked(parent_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm),
        Ghost(*initial_regs), Ghost(endpoint_index_opt),
    );
    proof {
        assert(new_process_trace_after_publish(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), old(steps).snapshot_u(), cpu_id,
            *source_range, *initial_regs, endpoint_index_opt, false)) by {
            new_process_trace_publish_step(&*steps, publish_before, old(steps).view().len() as int, old(steps).snapshot_u(), cpu_id, *source_range, *initial_regs, endpoint_index_opt, false);
        };
        assert(krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { reveal(container_allocator_wf); };
        assert(share_mapping_4k_source_range_present(krnl, source_pagetable_ptr, source_range)) by { reveal(PageTable::wf_mapping_4k); reveal(mapped_4k_page_pagetable_wf); source_range.va_range_lemma(); };
    }
    proof {
        assert(lctx.thread_lock_map().dom() == set![current_thread_ptr, current_thread_ptr]) by { vstd::set::axiom_set_ext_equal(lctx.thread_lock_map().dom(), set![current_thread_ptr, current_thread_ptr]); };
        assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable_ptr, container_ptr, source_range)) by { source_range.va_range_lemma(); reveal(mapped_4k_page_pagetable_wf); reveal(container_process_page_pagetable_wf); reveal(process_thread_wf); reveal(container_subtree_set_exclusive); };
        assert(krnl.pt_mp.spec_index(target_pagetable_ptr).view().spec_mapping_4k_va_range_empty(source_range.start, source_range.view().spec_index((source_range.len - 1) as int))) by { reveal(PageTable::spec_mapping_4k_va_range_empty); };
    }
    proof {
        use_type_invariant(&*steps);
        assert({
            &&& share_4k_objects_k(*krnl, cpu_id).source_thread == current_thread_ptr && share_4k_objects_k(*krnl, cpu_id).quota_thread == current_thread_ptr
            &&& share_4k_objects_k(*krnl, cpu_id).target == child_ptr && share_4k_objects_k(*krnl, cpu_id).target_container == container_ptr
            &&& share_4k_objects_k(*krnl, cpu_id).transfer_source is None
        }) by { reveal(share_4k_objects_k); };
    }
    let ghost origin = Share4kOrigin::NewProcess(NewProcessProgress {
        range: *source_range, regs: *initial_regs, endpoint_index: endpoint_index_opt, with_iommu: false, child: Some(child_ptr),
    });
    let ghost share_before = steps.view();
    share_mapping_4k_build_and_share(
        krnl, source_range, source_range, allocator_ptr, current_thread_ptr, current_thread_ptr, current_thread_ptr, child_ptr, container_ptr, cpu_id,
        source_pagetable_ptr, target_pagetable_ptr, None, Ghost(origin), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm),
        Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm), Tracked(&target_pagetable_lock_perm), Tracked(None), Tracked(None),
    );
    proof {
        assert(new_process_trace_after_share(steps.view(), old(steps).view().len() as int, old(steps).snapshot_u(), cpu_id, *source_range, *initial_regs, endpoint_index_opt, false)) by {
            new_process_trace_share_steps(&*steps, share_before, old(steps).view().len() as int, old(steps).snapshot_u(), cpu_id, *source_range, *initial_regs, endpoint_index_opt, false);
        };
        assert(krnl.sched_mp.dom().contains(scheduler_ptr) && krnl.sched_mp.lock_id_by_key(scheduler_ptr).major == SCHEDULER_LOCK_MAJOR) by { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr); reveal(scheduler_perms_wf); };
    }
    let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler(scheduler_ptr, Tracked(&mut *lctx));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };

        assert(!krnl.prc_mp.spec_index(child_ptr).view().zombie) by { reveal(process_pagetable_match); };
    }
    proof {
        if let Some(endpoint_ptr) = endpoint {
            assert({
                &&& krnl.ep_mp.dom().contains(endpoint_ptr)
                &&& krnl.ep_mp.spec_index(endpoint_ptr).is_init()
                &&& typed_lock_map_contains_mode(lctx.endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
                &&& !krnl.ep_mp.spec_index(endpoint_ptr).being_killed()
                &&& krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
                &&& endpoint_lock_perm->Some_0.lock_id() == krnl.ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
            }) by { endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr); };
            assert(krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf() && krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr)) by { thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); reveal(thread_endpoint_ref_counter_wf); };
            assert(krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)) by { container_endpoint_wf_at(krnl.ctn_mp, krnl.ep_mp, endpoint_ptr); };
            assert({
                ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
                ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(container_ptr)
            }) by { reveal(container_thread_endpoint_wf); };
        }
    }
    proof { assert(krnl.prc_mp.spec_index(child_ptr).view().pagetable == target_pagetable_ptr) by { reveal(process_pagetable_match); }; }
    let ghost finish_before = steps.view();
    let new_thread_ptr = create_initial_thread_and_finish_new_process(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, child_ptr, current_thread_ptr, scheduler_ptr,
        endpoint, endpoint_index, source_pagetable_ptr, target_pagetable_ptr, None, Tracked(cpu_lock_perm),
        Tracked(child_lock_perm), Tracked(current_thread_lock_perm), Tracked(scheduler_lock_perm), Tracked(endpoint_lock_perm),
        Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(None), initial_regs,
    );
    proof {
        assert(new_process_commit_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), old(steps).snapshot_u(), cpu_id,
            *source_range, *initial_regs, endpoint_index_opt, false)) by {
            new_process_trace_finish_step(&*steps, finish_before, old(steps).view().len() as int, old(steps).snapshot_u(), cpu_id, *source_range, *initial_regs, endpoint_index_opt, false);
        };
    }
    (child_ptr, new_thread_ptr)
}
}
