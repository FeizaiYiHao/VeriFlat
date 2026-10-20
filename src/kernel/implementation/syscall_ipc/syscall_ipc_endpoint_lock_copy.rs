use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_endpoint::ipc_copy_endpoint_reference;
use super::syscall_ipc_spec::*;

verus! {
/// Write-locks the payload endpoint and copies the reference into the receiver's slot when the receiver's container may hold it;
/// returns the owner-check result with the endpoint lock.
pub(super) fn ipc_endpoint_lock_and_copy(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr,
    peer_thread_ptr: RwLockThreadPtr, receiver_thread_ptr: RwLockThreadPtr, payload_endpoint_ptr: RwLockEndpointPtr, source_endpoint_index: EndpointIdx,
    target_endpoint_index: EndpointIdx, Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (RetValueType, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
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
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
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
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), payload_endpoint_ptr, TypedLockMode::Write),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        final(lctx).container_lock_map().dom().is_empty(),
        final(lctx).process_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        final(lctx).endpoint_lock_map().dom() =~= set![payload_endpoint_ptr],
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom().is_empty(),
        final(lctx).pagetable_window_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        final(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        final(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        final(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        final(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        final(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        final(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        final(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        old(krnl).ep_mp.spec_index(payload_endpoint_ptr).locking_thread() is None,
        ({
            let owner = old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_container;
            let container = old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().owning_container;
            &&& old(krnl).ctn_mp.dom().contains(container)
            &&& ret.0 == if owner == container || old(krnl).ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(owner) {
                RetValueType::Success
            } else { RetValueType::ErrorIpcEndpointOwnerMismatch }
        }),
        *final(krnl) == (KernelK { thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, ..*old(krnl) }),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, receiver_thread_ptr),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(receiver_thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(receiver_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(receiver_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view() == (Thread {
            endpoint_descriptors: final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors,
            ..old(krnl).thr_mp.spec_index(receiver_thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view() == if ret.0 is Success {
            old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view().update(target_endpoint_index as int, Some(payload_endpoint_ptr))
        } else { old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view() },
        final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, payload_endpoint_ptr),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).being_killed() == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).being_killed(),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().queue.view() == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().queue.view(),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().queue_state == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().queue_state,
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_container == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_container,
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view() == if ret.0 is Success {
            old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view().insert((receiver_thread_ptr, target_endpoint_index))
        } else { old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view() },
        final(krnl).ep_mp.dom().contains(payload_endpoint_ptr),
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).ep_mp.spec_index(payload_endpoint_ptr).locking_thread()->Write_lock_id,
{
    proof {
        assert(krnl.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) by { reveal(LockedArray::typed_lock_map_aligned); };
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, current_thread_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, peer_thread_ptr);
    }
    let receiver_lock_perm = Tracked(if receiver_thread_ptr == current_thread_ptr { current_thread_lock_perm } else { peer_thread_lock_perm });
    let Tracked(payload_endpoint_lock_perm) = krnl.wlock_endpoint(payload_endpoint_ptr, Tracked(&mut *lctx));
    proof { endpoint_perms_wf_map(krnl.ep_mp); thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); }
    let payload_endpoint_ref = krnl.ep_mp.borrow_typed(payload_endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&payload_endpoint_lock_perm));
    let endpoint_owner = payload_endpoint_ref.owning_container;
    let receiver_container = krnl.thr_mp.borrow_typed(receiver_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), receiver_lock_perm).owning_container;
    proof { container_endpoint_wf_at(krnl.ctn_mp, krnl.ep_mp, payload_endpoint_ptr); }
    let owner_compatible = if endpoint_owner == receiver_container { true } else { container_tree_check_is_ancestor(krnl.rt_ctn, &krnl.ctn_mp, endpoint_owner, receiver_container) };
    let result = if owner_compatible {
        ipc_copy_endpoint_reference(krnl, receiver_thread_ptr, target_endpoint_index, payload_endpoint_ptr, Tracked(&*lctx), receiver_lock_perm, Tracked(&payload_endpoint_lock_perm));
        RetValueType::Success
    } else {
        RetValueType::ErrorIpcEndpointOwnerMismatch
    };
    (result, Tracked(payload_endpoint_lock_perm))
}
}
