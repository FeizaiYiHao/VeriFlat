use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_endpoint::ipc_finish_endpoint_transit;
use super::syscall_ipc_endpoint_lock_copy::ipc_endpoint_lock_and_copy;
use super::syscall_ipc_spec::*;

verus! {
/// Locked phase of `ipc_rendezvous_endpoint` after the transit step: write-locks the payload endpoint, copies the reference when
/// the receiver may hold it, write-locks the peer's scheduler shard, and finishes the transit step with the owner-check result.
pub(super) fn ipc_endpoint_copy_and_finish_transit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, receiver_thread_ptr: RwLockThreadPtr,
    payload_endpoint_ptr: RwLockEndpointPtr, source_endpoint_index: EndpointIdx, target_endpoint_index: EndpointIdx,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(peer_thread_lock_perm): Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        current_thread_ptr != peer_thread_ptr,
        receiver_thread_ptr == current_thread_ptr || receiver_thread_ptr == peer_thread_ptr,
        edp_idx_valid(source_endpoint_index),
        edp_idx_valid(target_endpoint_index),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcEndpoint {
            peer: peer_thread_ptr, caller_sends: receiver_thread_ptr == peer_thread_ptr,
            payload_index: if receiver_thread_ptr == peer_thread_ptr { source_endpoint_index } else { target_endpoint_index },
        }),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).is_init(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == (IPCPayLoad::Endpoint { endpoint_index: if receiver_thread_ptr == peer_thread_ptr { target_endpoint_index } else { source_endpoint_index } }),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(if receiver_thread_ptr == peer_thread_ptr { current_thread_ptr } else { peer_thread_ptr }).view().endpoint_descriptors.view()[source_endpoint_index as int] == Some(payload_endpoint_ptr),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view()[target_endpoint_index as int] is None,
        old(krnl).ep_mp.dom().contains(payload_endpoint_ptr),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
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
        ret == ipc_endpoint_finish_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id),
        ret is Success || ret is ErrorIpcEndpointOwnerMismatch,
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
    proof {
        assert(krnl.prc_mp.dom().contains(process_ptr)) by { process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); };
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, current_thread_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, peer_thread_ptr);
        krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), current_thread_ptr);
        krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), peer_thread_ptr);
    }
    let (result, Tracked(payload_endpoint_lock_perm)) = ipc_endpoint_lock_and_copy(
        krnl, Tracked(&mut *lctx), cpu_id, process_ptr, current_thread_ptr, peer_thread_ptr, receiver_thread_ptr, payload_endpoint_ptr, source_endpoint_index,
        target_endpoint_index, Tracked(&current_thread_lock_perm), Tracked(&peer_thread_lock_perm),
    );
    proof { thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr); thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); }
    let peer_thread_ref = krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
    let peer_container_ptr = peer_thread_ref.owning_container;
    let peer_last_cpu = peer_thread_ref.last_cpu;
    let caller_container_ptr = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm)).owning_container;
    let wake_cpu = if peer_container_ptr == caller_container_ptr { cpu_id } else { peer_last_cpu };
    proof { container_perms_wf_at(krnl.ctn_mp, peer_container_ptr); }
    let peer_scheduler_ptr = krnl.ctn_mp.borrow_rodata(peer_container_ptr).borrow().scheduler;
    proof { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, peer_container_ptr); }
    let Tracked(peer_scheduler_lock_perm) = krnl.wlock_scheduler_shard(peer_scheduler_ptr, wake_cpu, Tracked(&mut *lctx));
    proof { container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, peer_scheduler_ptr, wake_cpu, peer_thread_ptr); }
    ipc_finish_endpoint_transit(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, payload_endpoint_ptr, peer_thread_ptr, peer_scheduler_ptr,
        wake_cpu, result, Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm), Tracked(payload_endpoint_lock_perm),
        Ghost(receiver_thread_ptr), Ghost(target_endpoint_index), Ghost(source_endpoint_index), Tracked(peer_thread_lock_perm), Tracked(peer_scheduler_lock_perm),
    )
}
}
