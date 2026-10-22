use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_endpoint_spec::ipc_finish_endpoint_transit_eof_transition_framing;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
/// Releases the caller, the scheduled transit peer, the peer's scheduler shard, the payload endpoint, and the cpu after the
/// transition `cleared` → `*old(krnl)` summarized by `ipc_finish_endpoint_transit_eof_transition_framing`, where `cleared` is `transit_k`
/// with the caller's progress and the peer's partner cleared, and records the finish step.
pub(super) fn ipc_finish_endpoint_transit_release_and_end_step(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, payload_endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, wake_cpu: CpuId, result: RetValueType, Ghost(transit_k): Ghost<KernelK>, Ghost(cleared): Ghost<KernelK>, Ghost(receiver_thread_ptr): Ghost<RwLockThreadPtr>,
    Ghost(target_endpoint_index): Ghost<EndpointIdx>, Ghost(source_endpoint_index): Ghost<EndpointIdx>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(payload_endpoint_lock_perm): Tracked<LockPerm>, Tracked(peer_thread_lock_perm): Tracked<LockPerm>,
    Tracked(peer_scheduler_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        receiver_thread_ptr == current_thread_ptr || receiver_thread_ptr == peer_thread_ptr,
        edp_idx_valid(source_endpoint_index),
        edp_idx_valid(target_endpoint_index),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        old(steps).snapshot_k().thr_mp.dom().contains(current_thread_ptr),
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).locking_thread() is Write,
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcEndpoint {
            peer: peer_thread_ptr, caller_sends: receiver_thread_ptr == peer_thread_ptr,
            payload_index: if receiver_thread_ptr == peer_thread_ptr { source_endpoint_index } else { target_endpoint_index },
        }),
        old(steps).snapshot_k().thr_mp.spec_index(peer_thread_ptr).locking_thread() is Write,
        old(steps).snapshot_k().ctn_mp.dom().contains(old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).view().owning_container),
        old(steps).snapshot_k().ctn_mp.dom().contains(old(steps).snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().owning_container),
        old(steps).snapshot_k().ep_mp.dom().contains(payload_endpoint_ptr),
        old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).locking_thread() is None,
        wake_cpu == if old(steps).snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().owning_container == old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).view().owning_container {
            cpu_id
        } else { old(steps).snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().last_cpu },
        transit_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        transit_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        transit_k.prc_mp.dom().contains(process_ptr),
        old(steps).snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == (IPCPayLoad::Endpoint { endpoint_index: if receiver_thread_ptr == peer_thread_ptr { target_endpoint_index } else { source_endpoint_index } }),
        old(steps).snapshot_k().thr_mp.spec_index(if receiver_thread_ptr == peer_thread_ptr { current_thread_ptr } else { peer_thread_ptr }).view().endpoint_descriptors.view()[source_endpoint_index as int] == Some(payload_endpoint_ptr),
        {
            let owner = old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().owning_container;
            let container = old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).view().owning_container;
            &&& old(steps).snapshot_k().ctn_mp.dom().contains(container)
            &&& result == if owner == container || old(steps).snapshot_k().ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(owner) {
                RetValueType::Success
            } else { RetValueType::ErrorIpcEndpointOwnerMismatch }
        },
        transit_k == (KernelK { thr_mp: transit_k.thr_mp, ep_mp: transit_k.ep_mp, sched_mp: transit_k.sched_mp, ..old(steps).snapshot_k() }),
        transit_k.thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, receiver_thread_ptr),
        transit_k.thr_mp.spec_index(receiver_thread_ptr).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).locking_thread(),
        transit_k.thr_mp.spec_index(receiver_thread_ptr).being_killed() == old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).being_killed(),
        transit_k.thr_mp.spec_index(receiver_thread_ptr).view() == (Thread {
            endpoint_descriptors: transit_k.thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors,
            ..old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).view()
        }),
        transit_k.thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view() == if result is Success {
            old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view().update(target_endpoint_index as int, Some(payload_endpoint_ptr))
        } else { old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view() },
        transit_k.ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, payload_endpoint_ptr),
        transit_k.ep_mp.spec_index(payload_endpoint_ptr).being_killed() == old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).being_killed(),
        transit_k.ep_mp.spec_index(payload_endpoint_ptr).view().queue.view() == old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().queue.view(),
        transit_k.ep_mp.spec_index(payload_endpoint_ptr).view().queue_state == old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().queue_state,
        transit_k.ep_mp.spec_index(payload_endpoint_ptr).view().owning_container == old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().owning_container,
        transit_k.ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view() == if result is Success {
            old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view().insert((receiver_thread_ptr, target_endpoint_index))
        } else { old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view() },
        transit_k.sched_mp.dom() == old(steps).snapshot_k().sched_mp.dom(),
        forall|p: RwLockSchedulerPtr| #![trigger transit_k.sched_mp.spec_index(p)]
            transit_k.sched_mp.dom().contains(p) ==> scheduler_shards_of(transit_k.sched_mp.spec_index(p)) == scheduler_shards_of(old(steps).snapshot_k().sched_mp.spec_index(p)),
        old(steps).snapshot_k().thr_mp.dom().contains(peer_thread_ptr),
        old(steps).snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT,
        current_thread_ptr != peer_thread_ptr,
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, wake_cpu),
        transit_k.thr_mp.dom().contains(current_thread_ptr),
        transit_k.thr_mp.dom().contains(peer_thread_ptr),
        transit_k.ctn_mp.spec_index(transit_k.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().scheduler == peer_scheduler_ptr,
        ipc_finish_endpoint_transit_eof_transition_framing(cleared, *old(krnl), current_thread_ptr, peer_thread_ptr, peer_scheduler_ptr, wake_cpu, result),
        cleared == (KernelK { thr_mp: cleared.thr_mp, ..transit_k }),
        cleared.thr_mp.dom() == transit_k.thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger cleared.thr_mp.spec_index(t)]
            transit_k.thr_mp.dom().contains(t) && t != current_thread_ptr && t != peer_thread_ptr ==> cleared.thr_mp.spec_index(t) == transit_k.thr_mp.spec_index(t),
        {
            let current_before = transit_k.thr_mp.spec_index(current_thread_ptr);
            let current_after = cleared.thr_mp.spec_index(current_thread_ptr);
            let peer_before = transit_k.thr_mp.spec_index(peer_thread_ptr);
            let peer_after = cleared.thr_mp.spec_index(peer_thread_ptr);
            &&& current_after.view() == (Thread { syscall_progress: current_after.view().syscall_progress, ..current_before.view() })
            &&& current_after.locking_thread() == current_before.locking_thread() && current_after.being_killed() == current_before.being_killed()
            &&& peer_after.view() == peer_before.view() && peer_after.locking_thread() == peer_before.locking_thread() && peer_after.being_killed() == peer_before.being_killed()
        },
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(payload_endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), payload_endpoint_ptr, TypedLockMode::Write),
        payload_endpoint_lock_perm.state() is WriteLock,
        payload_endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
        payload_endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::SCHEDULED { cpu_id: wake_cpu }),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(peer_scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (peer_scheduler_ptr, wake_cpu), TypedLockMode::Write),
        peer_scheduler_lock_perm.state() is WriteLock,
        peer_scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(peer_scheduler_ptr).shards.spec_index(wake_cpu).view().locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![payload_endpoint_ptr],
        old(lctx).scheduler_lock_map().dom() =~= set![(peer_scheduler_ptr, wake_cpu)],
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
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
{
    hide(Set::is_empty);
    krnl.wunlock_thread(peer_thread_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm));
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    krnl.wunlock_scheduler_shard(peer_scheduler_ptr, wake_cpu, Tracked(&mut *lctx), Tracked(peer_scheduler_lock_perm));
    krnl.wunlock_endpoint(payload_endpoint_ptr, Tracked(&mut *lctx), Tracked(payload_endpoint_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        reveal(ipc_finish_endpoint_transit_eof_transition_framing);
        assert(kernel_thread_state_changed(&steps.snapshot_k(), &*krnl, peer_thread_ptr)) by { reveal(kernel_thread_state_changed); };
        let pre_k = steps.snapshot_k();
        let descriptor = if result is Success { Some((receiver_thread_ptr, target_endpoint_index)) } else { None };
        reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        ipc_endpoint_finish_step_pre_from_k(&pre_k, cpu_id, process_ptr, current_thread_ptr, peer_thread_ptr, payload_endpoint_ptr, receiver_thread_ptr, source_endpoint_index,
            target_endpoint_index, result, wake_cpu);
        kernel_peer_scheduled_and_locks_released_implies_u_step(&pre_k, &*krnl, cpu_id, current_thread_ptr, peer_thread_ptr, wake_cpu, payload_endpoint_ptr, result, false, descriptor);
        ipc_endpoint_finish_step_from_u(kernel_k_to_kernel_u(pre_k), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, current_thread_ptr, peer_thread_ptr, payload_endpoint_ptr,
            receiver_thread_ptr, source_endpoint_index, target_endpoint_index, result, descriptor, wake_cpu);
        let ghost old_state = steps.snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().state;
        let ghost new_state = krnl.thr_mp.spec_index(peer_thread_ptr).view().state;
        steps.end_kernel_step_thread_state_changed(&*krnl, &*lctx, peer_thread_ptr, old_state, new_state,);
    }
}
} // verus!
