use vstd::prelude::*;
use crate::*;
use super::*;
use super::syscall_new_container_spec::*;
use super::syscall_new_container_trace::*;

verus! {
/// Records the new-container progress on the caller thread and ends the enter step.
pub(super) fn enter_new_container_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, caller_cpu_id: CpuId,
    parent_ctn_ptr: RwLockContainerPtr, parent_prc_ptr: RwLockProcessPtr, current_thrd_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot,
    source_range: &VaRange4K, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, parent_cpu_set: RwLockCpuSetPtr,
    endpoint: Option<RwLockEndpointPtr>, ep_idx: EndpointIdx, Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Ghost(regs): Ghost<Registers>,
)
    requires
        index_valid(NUM_CPUS, caller_cpu_id),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp,
            thrd_mp: old(krnl).thrd_mp, ep_mp: old(krnl).ep_mp, pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, cpu_set_mp: old(krnl).cpu_set_mp, ..old(steps).snapshot_k() }),
        match endpoint { Some(e) => old(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, e), None => old(krnl).ep_mp == old(steps).snapshot_k().ep_mp },
        endpoint is Some ==> old(steps).snapshot_k().ep_mp.spec_index(endpoint->Some_0).locking_thread() is None,
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, caller_cpu_id),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(caller_cpu_id as int, CpuOpState::InStep),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, parent_ctn_ptr),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, parent_prc_ptr),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, current_thrd_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, source_pagetable_ptr),
        old(krnl).pt_lower.view() =~= old(steps).snapshot_k().pt_lower.view().insert(source_pagetable_ptr, old(krnl).pt_lower.view().spec_index(source_pagetable_ptr)),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).lower.pagetable_window_locks
            == pagetable_window_locks_after_locking_range(whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), source_pagetable_ptr).lower.pagetable_window_locks, *source_range, caller_cpu_id),
        old(steps).snapshot_k().cpu_arr.spec_index(caller_cpu_id).value.locking_thread() is None,
        old(steps).snapshot_k().ctn_mp.spec_index(parent_ctn_ptr).locking_thread() is None,
        old(steps).snapshot_k().prc_mp.spec_index(parent_prc_ptr).locking_thread() is None,
        old(steps).snapshot_k().thrd_mp.spec_index(current_thrd_ptr).locking_thread() is None,
        !(old(steps).snapshot_k().pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Write),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).lock_state_u() == old(steps).snapshot_k().pt_mp.spec_index(source_pagetable_ptr).lock_state_u().with_reader(caller_cpu_id),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().state == CpuState::Running,
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_thread == Some(current_thrd_ptr),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &KernelK { cpu_set_mp: old(steps).snapshot_k().cpu_set_mp, ..*old(krnl) }),
        old(krnl).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, parent_cpu_set),
        old(steps).snapshot_k().cpu_set_mp.spec_index(parent_cpu_set).locking_thread() is None,
        !old(steps).snapshot_k().cpu_set_mp.spec_index(parent_cpu_set).being_killed() && !old(krnl).cpu_set_mp.spec_index(parent_cpu_set).being_killed(),
        caller_cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_hw_cr3_pcid[caller_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_pcid),
        process_quota_4k <= funding_page_count,
        funding_page_count <= usize::MAX - 9 - 3 * source_range.len,
        source_range.wf(),
        source_range.len > 0,
        source_range.len <= (usize::MAX - 9) / 3,
        index_valid(NUM_CPUS, transfer_cpu_id),
        old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off,
        old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == parent_ctn_ptr,
        transfer_cpu_id != caller_cpu_id,
        old(krnl).cpu_set_mp.dom().contains(parent_cpu_set),
        old(krnl).cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id),
        old(krnl).ctn_mp.spec_index(parent_ctn_ptr).view_rodata().view().cpu_set == parent_cpu_set,
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), parent_cpu_set, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).mapping_4k().dom().contains(source_range.view().spec_index(j))
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).mapping_4k().spec_index(source_range.view().spec_index(j)).present
        },
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_ctn_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_prc_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thrd_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> {
            let ep_ptr = endpoint->Some_0;
            &&& edp_idx_valid(ep_idx)
            &&& old(lctx).endpoint_lock_map().dom() =~= set![ep_ptr]
            &&& old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.wf()
            &&& old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.spec_index(ep_idx) == endpoint
            &&& old(krnl).ep_mp.dom().contains(ep_ptr)
            &&& old(krnl).ep_mp.spec_index(ep_ptr).is_init()
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), ep_ptr, TypedLockMode::Write)
            &&& !old(krnl).ep_mp.spec_index(ep_ptr).being_killed()
            &&& old(krnl).ep_mp.spec_index(ep_ptr).view().owning_threads.view().contains((current_thrd_ptr, ep_idx))
        },
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![parent_cpu_set],
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(caller_cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().owning_container == parent_ctn_ptr,
        old(krnl).ctn_mp.dom().contains(parent_ctn_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_ctn_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_ctn_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(parent_ctn_ptr).view().zombie,
        old(krnl).ctn_mp.spec_index(parent_ctn_ptr).lock_process_owner_u() == Some(LockOwnerId::Some(old(krnl).prc_mp.spec_index(parent_prc_ptr).view_rodata().view().depth)),
        old(krnl).ctn_mp.spec_index(parent_ctn_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        old(krnl).prc_mp.dom().contains(parent_prc_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_prc_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_prc_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_prc_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(parent_prc_ptr).view().state.view() is Zombie,
        old(krnl).prc_mp.spec_index(parent_prc_ptr).view_rodata().view().owning_container == parent_ctn_ptr,
        old(krnl).thrd_mp.dom().contains(current_thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
        !old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_container == parent_ctn_ptr,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_proc == parent_prc_ptr,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id: caller_cpu_id }),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_4k >= 9 + funding_page_count + 3 * source_range.len,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().quota_2m >= 2,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Read),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view().len() == old(steps).view().len() + 1,
        new_container_trace_after_enter(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), caller_cpu_id,
            *source_range, funding_page_count, process_quota_4k, transfer_cpu_id, regs, if endpoint is Some { Some(ep_idx) } else { None }),
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
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(krnl).cpu_arr.spec_index(caller_cpu_id).view() == old(krnl).cpu_arr.spec_index(caller_cpu_id).view(),
        final(krnl).cpu_hw_cr3_pcid[caller_cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[caller_cpu_id as int].view(),
        final(krnl).ctn_mp.dom().contains(parent_ctn_ptr),
        final(krnl).ctn_mp.spec_index(parent_ctn_ptr) == old(krnl).ctn_mp.spec_index(parent_ctn_ptr),
        final(krnl).prc_mp.dom().contains(parent_prc_ptr),
        final(krnl).prc_mp.spec_index(parent_prc_ptr) == old(krnl).prc_mp.spec_index(parent_prc_ptr),
        final(krnl).thrd_mp.dom().contains(current_thrd_ptr),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).view() == (Thread {
            syscall_progress: Ghost(Some(SyscallProgress::NewContainer(NewContainerProgress {
                range: *source_range, funding: funding_page_count, process_quota: process_quota_4k, transfer_cpu: transfer_cpu_id, regs,
                endpoint_index: if endpoint is Some { Some(ep_idx) } else { None }, child_container: None,
            }))),
            ..old(krnl).thrd_mp.spec_index(current_thrd_ptr).view()
        }),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
        final(krnl).cpu_set_mp.dom().contains(parent_cpu_set),
        final(krnl).cpu_set_mp.spec_index(parent_cpu_set) == old(krnl).cpu_set_mp.spec_index(parent_cpu_set),
        endpoint is Some ==> final(krnl).ep_mp.dom().contains(endpoint->Some_0) && final(krnl).ep_mp.spec_index(endpoint->Some_0) == old(krnl).ep_mp.spec_index(endpoint->Some_0),
{
    let ghost endpoint_index_opt: Option<EndpointIdx> = if endpoint is Some { Some(ep_idx) } else { None };
    let ghost record = NewContainerProgress {
        range: *source_range, funding: funding_page_count, process_quota: process_quota_4k, transfer_cpu: transfer_cpu_id, regs,
        endpoint_index: endpoint_index_opt, child_container: None,
    };
    let ghost progress = SyscallProgress::NewContainer(record);
    krnl.set_thread_syscall_progress(current_thrd_ptr, Ghost(Some(progress)), Tracked(&*lctx), Tracked(current_thread_lock_perm));
    proof {
        let ghost entered_k = *krnl;
        assert(steps.snapshot_k().thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, current_thrd_ptr);
        assert(new_container_trace_after_enter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), old(steps).snapshot_u(), caller_cpu_id,
            *source_range, funding_page_count, process_quota_4k, transfer_cpu_id, regs, endpoint_index_opt)) by {
            process_thread_wf_thread_at(old(krnl).prc_mp, old(krnl).thrd_mp, current_thrd_ptr); thread_cpu_wf_cpu_at(old(krnl).thrd_mp, old(krnl).cpu_arr, caller_cpu_id); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            kernel_cpu_process_thread_endpoint_wlocked_pagetable_rlocked_implies_u_step(&old(steps).snapshot_k(), old(krnl), old(lctx), caller_cpu_id, parent_prc_ptr,
                current_thrd_ptr, endpoint, Some(parent_ctn_ptr), Some(KernelK { cpu_set_mp: old(steps).snapshot_k().cpu_set_mp, ..*old(krnl) }));
            kernel_thread_syscall_progress_changed_implies_u_step(old(krnl), &entered_k, current_thrd_ptr);
            new_container_enter_step_from_u(old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), old(krnl), caller_cpu_id, parent_prc_ptr,
                current_thrd_ptr, parent_ctn_ptr, endpoint, *source_range, funding_page_count, process_quota_4k, transfer_cpu_id, regs, endpoint_index_opt,
                whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), source_pagetable_ptr).lower.pagetable_window_locks,
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).lower.pagetable_window_locks);
            new_container_trace_enter_step(&*steps, old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(entered_k), caller_cpu_id, *source_range,
                funding_page_count, process_quota_4k, transfer_cpu_id, regs, endpoint_index_opt);
        };
    }
}
} // verus!
