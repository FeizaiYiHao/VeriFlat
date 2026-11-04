use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_endpoint_spec::ipc_finish_transit_eof_transition_framing;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
/// Releases the caller, the scheduled transit peer, the peer's scheduler shard, the payload endpoint, and the cpu after the
/// transition `transit_k` → `*old(krnl)` summarized by `ipc_finish_transit_eof_transition_framing`, and records the finish step.
pub(super) fn ipc_finish_endpoint_transit_release_and_end_step(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    prc_ptr: RwLockProcessPtr, current_thrd_ptr: RwLockThreadPtr, payload_ep_ptr: RwLockEndpointPtr, peer_thrd_ptr: RwLockThreadPtr,
    peer_sched_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, result: RetValueType, Ghost(transit_k): Ghost<KernelK>, Ghost(receiver_thrd_ptr): Ghost<RwLockThreadPtr>,
    Ghost(target_ep_idx): Ghost<EndpointIdx>, Ghost(source_ep_idx): Ghost<EndpointIdx>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(payload_endpoint_lock_perm): Tracked<LockPerm>, Tracked(peer_thread_lock_perm): Tracked<LockPerm>,
    Tracked(peer_scheduler_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        receiver_thrd_ptr == current_thrd_ptr || receiver_thrd_ptr == peer_thrd_ptr,
        edp_idx_valid(source_ep_idx),
        edp_idx_valid(target_ep_idx),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        old(steps).snapshot_k().thrd_mp.dom().contains(current_thrd_ptr),
        old(steps).snapshot_k().thrd_mp.spec_index(current_thrd_ptr).locking_thread() is Write,
        old(steps).snapshot_k().thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcEndpoint {
            peer: peer_thrd_ptr, caller_sends: receiver_thrd_ptr == peer_thrd_ptr,
            payload_index: if receiver_thrd_ptr == peer_thrd_ptr { source_ep_idx } else { target_ep_idx },
        }),
        old(steps).snapshot_k().thrd_mp.spec_index(peer_thrd_ptr).locking_thread() is Write,
        old(steps).snapshot_k().ctn_mp.dom().contains(old(steps).snapshot_k().thrd_mp.spec_index(current_thrd_ptr).view().owning_container),
        old(steps).snapshot_k().ctn_mp.dom().contains(old(steps).snapshot_k().thrd_mp.spec_index(peer_thrd_ptr).view().owning_container),
        old(steps).snapshot_k().ep_mp.dom().contains(payload_ep_ptr),
        old(steps).snapshot_k().ep_mp.spec_index(payload_ep_ptr).locking_thread() is None,
        wake_cpu == if old(steps).snapshot_k().thrd_mp.spec_index(peer_thrd_ptr).view().owning_container == old(steps).snapshot_k().thrd_mp.spec_index(current_thrd_ptr).view().owning_container {
            cpu_id
        } else { old(steps).snapshot_k().thrd_mp.spec_index(peer_thrd_ptr).view().last_cpu },
        transit_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        transit_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thrd_ptr),
        transit_k.prc_mp.dom().contains(prc_ptr),
        old(steps).snapshot_k().thrd_mp.spec_index(peer_thrd_ptr).view().ipc_payload == (IPCPayLoad::Endpoint { endpoint_index: if receiver_thrd_ptr == peer_thrd_ptr { target_ep_idx } else { source_ep_idx } }),
        old(steps).snapshot_k().thrd_mp.spec_index(if receiver_thrd_ptr == peer_thrd_ptr { current_thrd_ptr } else { peer_thrd_ptr }).view().endpoint_descriptors.view()[source_ep_idx as int] == Some(payload_ep_ptr),
        {
            let owner = old(steps).snapshot_k().ep_mp.spec_index(payload_ep_ptr).view().owning_container;
            let container = old(steps).snapshot_k().thrd_mp.spec_index(receiver_thrd_ptr).view().owning_container;
            &&& old(steps).snapshot_k().ctn_mp.dom().contains(container)
            &&& result == if owner == container || old(steps).snapshot_k().ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(owner) {
                RetValueType::Success
            } else { RetValueType::ErrorIpcEndpointOwnerMismatch }
        },
        transit_k == (KernelK { thrd_mp: transit_k.thrd_mp, ep_mp: transit_k.ep_mp, sched_mp: transit_k.sched_mp, ..old(steps).snapshot_k() }),
        transit_k.thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, receiver_thrd_ptr),
        transit_k.thrd_mp.spec_index(receiver_thrd_ptr).locking_thread() == old(steps).snapshot_k().thrd_mp.spec_index(receiver_thrd_ptr).locking_thread(),
        transit_k.thrd_mp.spec_index(receiver_thrd_ptr).being_killed() == old(steps).snapshot_k().thrd_mp.spec_index(receiver_thrd_ptr).being_killed(),
        transit_k.thrd_mp.spec_index(receiver_thrd_ptr).view() == (Thread {
            endpoint_descriptors: transit_k.thrd_mp.spec_index(receiver_thrd_ptr).view().endpoint_descriptors,
            ..old(steps).snapshot_k().thrd_mp.spec_index(receiver_thrd_ptr).view()
        }),
        transit_k.thrd_mp.spec_index(receiver_thrd_ptr).view().endpoint_descriptors.view() == if result is Success {
            old(steps).snapshot_k().thrd_mp.spec_index(receiver_thrd_ptr).view().endpoint_descriptors.view().update(target_ep_idx as int, Some(payload_ep_ptr))
        } else { old(steps).snapshot_k().thrd_mp.spec_index(receiver_thrd_ptr).view().endpoint_descriptors.view() },
        transit_k.ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, payload_ep_ptr),
        transit_k.ep_mp.spec_index(payload_ep_ptr).being_killed() == old(steps).snapshot_k().ep_mp.spec_index(payload_ep_ptr).being_killed(),
        transit_k.ep_mp.spec_index(payload_ep_ptr).view().queue.view() == old(steps).snapshot_k().ep_mp.spec_index(payload_ep_ptr).view().queue.view(),
        transit_k.ep_mp.spec_index(payload_ep_ptr).view().queue_state == old(steps).snapshot_k().ep_mp.spec_index(payload_ep_ptr).view().queue_state,
        transit_k.ep_mp.spec_index(payload_ep_ptr).view().owning_container == old(steps).snapshot_k().ep_mp.spec_index(payload_ep_ptr).view().owning_container,
        transit_k.ep_mp.spec_index(payload_ep_ptr).view().owning_threads.view() == if result is Success {
            old(steps).snapshot_k().ep_mp.spec_index(payload_ep_ptr).view().owning_threads.view().insert((receiver_thrd_ptr, target_ep_idx))
        } else { old(steps).snapshot_k().ep_mp.spec_index(payload_ep_ptr).view().owning_threads.view() },
        transit_k.sched_mp.dom() == old(steps).snapshot_k().sched_mp.dom(),
        forall|p: RwLockSchedulerPtr| #![trigger transit_k.sched_mp.spec_index(p)]
            transit_k.sched_mp.dom().contains(p) ==> scheduler_shards_of(transit_k.sched_mp.spec_index(p)) == scheduler_shards_of(old(steps).snapshot_k().sched_mp.spec_index(p)),
        old(steps).snapshot_k().thrd_mp.dom().contains(peer_thrd_ptr),
        old(steps).snapshot_k().thrd_mp.spec_index(peer_thrd_ptr).view().state is IPC_TRANSIT,
        old(steps).snapshot_k().thrd_mp.spec_index(peer_thrd_ptr).view().state->IPC_TRANSIT_partner == current_thrd_ptr,
        current_thrd_ptr != peer_thrd_ptr,
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, wake_cpu),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        transit_k.thrd_mp.dom().contains(current_thrd_ptr),
        transit_k.thrd_mp.dom().contains(peer_thrd_ptr),
        transit_k.ctn_mp.spec_index(transit_k.thrd_mp.spec_index(peer_thrd_ptr).view().owning_container).view_rodata().view().scheduler == peer_sched_ptr,
        ipc_finish_transit_eof_transition_framing(transit_k, *old(krnl), current_thrd_ptr, peer_thrd_ptr, peer_sched_ptr, wake_cpu, result),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.dom().contains(current_thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed() == false,
        !old(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcEndpoint {
            peer: peer_thrd_ptr, caller_sends: receiver_thrd_ptr == peer_thrd_ptr,
            payload_index: if receiver_thrd_ptr == peer_thrd_ptr { source_ep_idx } else { target_ep_idx },
        }),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(payload_ep_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), payload_ep_ptr, TypedLockMode::Write),
        payload_endpoint_lock_perm.state() is WriteLock,
        payload_endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
        payload_endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(payload_ep_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.dom().contains(peer_thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thrd_ptr, TypedLockMode::Write),
        old(krnl).thrd_mp.spec_index(peer_thrd_ptr).being_killed() == false,
        !old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().state == (ThreadState::SCHEDULED { cpu_id: wake_cpu }),
        old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().syscall_progress.view() is None,
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(peer_thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(peer_sched_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (peer_sched_ptr, wake_cpu), TypedLockMode::Write),
        peer_scheduler_lock_perm.state() is WriteLock,
        peer_scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(peer_sched_ptr).shards.spec_index(wake_cpu).view().locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thrd_ptr, peer_thrd_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![payload_ep_ptr],
        old(lctx).scheduler_lock_map().dom() =~= set![(peer_sched_ptr, wake_cpu)],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
        ipc_endpoint_finish_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id),
        ipc_endpoint_finish_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id),
        result == ipc_endpoint_finish_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
{
    hide(Set::is_empty);
    krnl.wunlock_thread(peer_thrd_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm));
    krnl.set_thread_syscall_progress(current_thrd_ptr, Ghost(None), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
    krnl.wunlock_thread(current_thrd_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    krnl.wunlock_scheduler_shard(peer_sched_ptr, wake_cpu, Tracked(&mut *lctx), Tracked(peer_scheduler_lock_perm));
    krnl.wunlock_endpoint(payload_ep_ptr, Tracked(&mut *lctx), Tracked(payload_endpoint_lock_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        reveal(ipc_finish_transit_eof_transition_framing);
        assert(kernel_thread_state_changed(&steps.snapshot_k(), &*krnl, peer_thrd_ptr)) by { reveal(kernel_thread_state_changed); };
        let pre_k = steps.snapshot_k();
        let descriptor = if result is Success { Some((receiver_thrd_ptr, target_ep_idx)) } else { None };
        reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        ipc_endpoint_finish_step_pre_from_k(&pre_k, cpu_id, prc_ptr, current_thrd_ptr, peer_thrd_ptr, payload_ep_ptr, receiver_thrd_ptr, source_ep_idx,
            target_ep_idx, result, wake_cpu);
        kernel_peer_scheduled_and_locks_released_implies_u_step(&pre_k, &*krnl, cpu_id, current_thrd_ptr, peer_thrd_ptr, wake_cpu, payload_ep_ptr, result, false, descriptor);
        ipc_endpoint_finish_step_from_u(kernel_k_to_kernel_u(pre_k), kernel_k_to_kernel_u(*krnl), cpu_id, prc_ptr, current_thrd_ptr, peer_thrd_ptr, payload_ep_ptr,
            receiver_thrd_ptr, source_ep_idx, target_ep_idx, result, descriptor, wake_cpu);
        let ghost old_state = steps.snapshot_k().thrd_mp.spec_index(peer_thrd_ptr).view().state;
        let ghost new_state = krnl.thrd_mp.spec_index(peer_thrd_ptr).view().state;
        steps.end_kernel_step_thread_state_changed(&*krnl, &*lctx, peer_thrd_ptr, old_state, new_state,);
    }
}
} // verus!
