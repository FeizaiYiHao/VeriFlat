use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_queue::ipc_schedule_transit_peer;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_endpoint_eof::ipc_finish_transit_eof;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_endpoint_spec::ipc_finish_transit_eof_transition_framing;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
/// Finishes a pages rendezvous whose tables are released with `result`: write-locks the peer's scheduler shard, schedules the transit
/// peer with `result`, and releases the peer, the caller with its progress cleared, the shard, the channel, and the cpu as the finish step.
pub(super) fn ipc_finish_pages_transit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr, result: RetValueType, cpu_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<LockPerm>, peer_thread_lock_perm: Tracked<LockPerm>, Ghost(channel_index): Ghost<EndpointIdx>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        current_thread_ptr != peer_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        ({
            let progress = old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view();
            &&& progress is Some
            &&& progress->Some_0 is IpcPages
            &&& progress->Some_0->IpcPages_peer == peer_thread_ptr
            &&& progress->Some_0->IpcPages_released == Some(result)
            &&& progress->Some_0->IpcPages_tables is Unlocked
        }),
        edp_idx_valid(channel_index),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[channel_index as int] == Some(endpoint_ptr),
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
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is IPC_TRANSIT,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state->IPC_TRANSIT_partner == current_thread_ptr,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
        ipc_pages_finish_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, channel_index),
        ipc_pages_finish_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, channel_index),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret == result,
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
{
    hide(Set::is_empty);
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();
    proof { thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr); thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); }
    let peer_thread_ref = krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
    let peer_container_ptr = peer_thread_ref.owning_container;
    let peer_last_cpu = peer_thread_ref.last_cpu;
    let caller_container_ptr = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm)).owning_container;
    let wake_cpu = if peer_container_ptr == caller_container_ptr { cpu_id } else { peer_last_cpu };
    proof { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, peer_thread_ptr); container_perms_wf_at(krnl.ctn_mp, peer_container_ptr); }
    let peer_scheduler_ptr = krnl.ctn_mp.borrow_rodata(peer_container_ptr).borrow().scheduler;
    proof { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, peer_container_ptr); }
    let Tracked(peer_scheduler_lock_perm) = krnl.wlock_scheduler_shard(peer_scheduler_ptr, wake_cpu, Tracked(&mut *lctx));
    proof { container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, peer_scheduler_ptr, wake_cpu, peer_thread_ptr); }
    let ghost old_peer_thread_lock_id = krnl.thr_mp.lock_id_by_key(peer_thread_ptr);
    let ghost locked_k = *krnl;
    assert(krnl.sched_mp.spec_index(peer_scheduler_ptr).shard(wake_cpu).queue.length != usize::MAX) by { scheduler_queue_len_bounded(&*krnl, peer_scheduler_ptr, wake_cpu); };
    let (scheduler_node_addr, scheduler_node_perm) = ipc_schedule_transit_peer(&mut krnl.thr_mp, Tracked(&*lctx), peer_thread_ptr, wake_cpu, current_thread_ptr, result, Tracked(&peer_thread_lock_perm));
    scheduler_map_enqueue_scheduled_thread(&mut krnl.sched_mp, peer_scheduler_ptr, wake_cpu, peer_thread_ptr, scheduler_node_addr, scheduler_node_perm, Tracked(&*lctx), Tracked(&peer_scheduler_lock_perm));
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Thread(peer_thread_ptr), old_peer_thread_lock_id, krnl.thr_mp.lock_id_by_key(peer_thread_ptr));
        assert(ipc_finish_transit_eof_transition_framing(locked_k, *krnl, current_thread_ptr, peer_thread_ptr, peer_scheduler_ptr, wake_cpu, result)) by { reveal(ipc_finish_transit_eof_transition_framing); };
        ipc_finish_transit_eof(locked_k, *krnl, current_thread_ptr, peer_thread_ptr, peer_scheduler_ptr, wake_cpu, result);
    }
    krnl.wunlock_thread(peer_thread_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm));
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    krnl.wunlock_scheduler_shard(peer_scheduler_ptr, wake_cpu, Tracked(&mut *lctx), Tracked(peer_scheduler_lock_perm));
    krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
    assert(krnl.cpu_arr.spec_index(cpu_id).view().view_ghost() == Some(cpu_id)) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        reveal(ipc_finish_transit_eof_transition_framing);
        assert(kernel_thread_state_changed(&steps.snapshot_k(), &*krnl, peer_thread_ptr)) by { reveal(kernel_thread_state_changed); };
        let pre_k = steps.snapshot_k();
        reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        ipc_pages_finish_step_pre_from_k(&pre_k, &*old(lctx), cpu_id, process_ptr, current_thread_ptr, peer_thread_ptr, endpoint_ptr, channel_index, result, wake_cpu);
        kernel_peer_scheduled_and_locks_released_implies_u_step(&pre_k, &*krnl, cpu_id, current_thread_ptr, peer_thread_ptr, wake_cpu, endpoint_ptr, result, false, None);
        ipc_pages_finish_step_from_u(kernel_k_to_kernel_u(pre_k), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, current_thread_ptr, peer_thread_ptr, endpoint_ptr, channel_index,
            result, wake_cpu);
        let ghost old_state = steps.snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().state;
        let ghost new_state = krnl.thr_mp.spec_index(peer_thread_ptr).view().state;
        steps.end_kernel_step_thread_state_changed(&*krnl, &*lctx, peer_thread_ptr, old_state, new_state);
    }
    result
}
} // verus!
