use vstd::prelude::*;
use crate::*;
use super::syscall_new_process_spec::*;
use super::syscall_new_process_trace::*;

verus! {
/// Records the new-process progress on the caller thread and ends the enter step.
pub(super) fn enter_new_process_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, parent_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, source_pagetable_ptr: RwLockPageTableRoot, endpoint: Option<RwLockEndpointPtr>,
    endpoint_index: EndpointIdx, source_range: &VaRange4K, Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Ghost(regs): Ghost<Registers>, Ghost(with_iommu): Ghost<bool>,
)
    requires
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp,
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
        match endpoint { Some(e) => old(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, e), None => old(krnl).ep_mp == old(steps).snapshot_k().ep_mp },
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(parent_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            &&& edp_idx_valid(endpoint_index)
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == endpoint
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
        },
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        new_process_enter_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, *source_range, if endpoint is Some { Some(endpoint_index) } else { None }, with_iommu),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view().len() == old(steps).view().len() + 1,
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        new_process_trace_after_enter(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id,
            *source_range, regs, if endpoint is Some { Some(endpoint_index) } else { None }, with_iommu),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(krnl)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        containers_rodata_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp),
        final(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        final(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr) == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr),
        final(krnl).prc_mp.dom().contains(parent_ptr),
        final(krnl).prc_mp.spec_index(parent_ptr) == old(krnl).prc_mp.spec_index(parent_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view() == (Thread {
            syscall_progress: Ghost(Some(SyscallProgress::NewProcess(NewProcessProgress {
                range: *source_range, regs, endpoint_index: if endpoint is Some { Some(endpoint_index) } else { None }, with_iommu, child: None,
            }))),
            ..old(krnl).thr_mp.spec_index(current_thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr) == old(krnl).pt_mp.spec_index(source_pagetable_ptr),
        endpoint is Some ==> final(krnl).ep_mp.dom().contains(endpoint->Some_0) && final(krnl).ep_mp.spec_index(endpoint->Some_0) == old(krnl).ep_mp.spec_index(endpoint->Some_0),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, source_pagetable_ptr, final(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
{
    let ghost endpoint_index_opt: Option<EndpointIdx> = if endpoint is Some { Some(endpoint_index) } else { None };
    let ghost entry_u = kernel_k_to_kernel_u(old(steps).snapshot_k());
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(Some(SyscallProgress::NewProcess(NewProcessProgress {
        range: *source_range, regs, endpoint_index: endpoint_index_opt, with_iommu, child: None,
    }))), Tracked(&*lctx), Tracked(current_thread_lock_perm));
    proof {
        let ghost entered_k = *krnl;
        assert(steps.snapshot_k().thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, current_thread_ptr);
        assert(new_process_trace_after_enter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), entry_u, cpu_id,
            *source_range, regs, endpoint_index_opt, with_iommu)) by {
            process_thread_wf_at(old(krnl).prc_mp, old(krnl).thr_mp, current_thread_ptr); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(&old(steps).snapshot_k(), old(krnl), old(lctx),
                cpu_id, parent_ptr, current_thread_ptr, endpoint, true, None, true, None);
            kernel_thread_syscall_progress_changed_implies_u_step(old(krnl), &entered_k, current_thread_ptr);
            new_process_enter_step_from_u(entry_u, kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id, parent_ptr, current_thread_ptr, endpoint,
                *source_range, regs, endpoint_index_opt, with_iommu);
            new_process_trace_enter_step(&*steps, old(steps).view(), entry_u, kernel_k_to_kernel_u(entered_k), cpu_id, *source_range, regs, endpoint_index_opt, with_iommu);
        };
    }
}
} // verus!
