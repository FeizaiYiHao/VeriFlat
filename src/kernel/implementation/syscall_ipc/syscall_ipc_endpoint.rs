use vstd::prelude::*;

use crate::*;
use super::syscall_ipc_queue::{
    ipc_dequeue_endpoint_waiter,
    ipc_enqueue_scheduled_thread,
    ipc_move_endpoint_waiter_to_transit,
    ipc_schedule_endpoint_transit,
};
use super::syscall_ipc_transition::{
    ipc_schedule_waiting_peer_and_finish,
};

verus! {

pub(super) fn ipc_copy_endpoint_reference(
    krnl: &mut KernelK,
    receiver_thread_ptr: RwLockThreadPtr,
    target_endpoint_index: EndpointIdx,
    payload_endpoint_ptr: RwLockEndpointPtr,
    Tracked(lctx): Tracked<&LocalContext>,
    Tracked(receiver_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(payload_endpoint_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        lctx.kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), lctx),
        lock_id_set_aligned(lctx),
        old(krnl).thr_mp.dom().contains(receiver_thread_ptr),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).is_init(),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).wlocked_by(lctx),
        receiver_thread_lock_perm.state() is WriteLock,
        receiver_thread_lock_perm.thread_id() == lctx.thread_id(),
        receiver_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(receiver_thread_ptr).locking_thread()->Write_lock_id,
        edp_idx_valid(target_endpoint_index),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.spec_index(target_endpoint_index) is None,
        old(krnl).ep_mp.dom().contains(payload_endpoint_ptr),
        old(krnl).ep_mp.spec_index(payload_endpoint_ptr).is_init(),
        old(krnl).ep_mp.spec_index(payload_endpoint_ptr).wlocked_by(lctx),
        payload_endpoint_lock_perm.state() is WriteLock,
        payload_endpoint_lock_perm.thread_id() == lctx.thread_id(),
        payload_endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).locking_thread()->Write_lock_id,
        {
            let endpoint_owner = old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_container;
            &&& old(krnl).ctn_mp.dom().contains(endpoint_owner)
            &&& {
                let receiver_container = old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().owning_container;
                ||| endpoint_owner == receiver_container
                ||| old(krnl).ctn_mp.spec_index(endpoint_owner).view().subtree_set.view().contains(receiver_container)
            }
        },
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        lock_id_set_aligned(lctx),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, receiver_thread_ptr),
        final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, payload_endpoint_ptr),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).wlocked_by(lctx),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(receiver_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().state == old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(receiver_thread_ptr).view()),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_4k == old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_4k,
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_2m,
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_1g,
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(receiver_thread_ptr).locking_thread(),
        final(krnl).thr_mp.lock_id_by_key(receiver_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(receiver_thread_ptr),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).wlocked_by(lctx),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).locking_thread() == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).locking_thread(),
        final(krnl).ep_mp.lock_id_by_key(payload_endpoint_ptr) == old(krnl).ep_mp.lock_id_by_key(payload_endpoint_ptr),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view() =~= old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view().update(target_endpoint_index as int, Some(payload_endpoint_ptr)),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view() =~= old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view().insert((receiver_thread_ptr, target_endpoint_index)),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().rf_counter == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().rf_counter + 1,
        final(krnl).pt_mp == old(krnl).pt_mp,
        final(krnl).it_mp == old(krnl).it_mp,
        final(krnl).irt == old(krnl).irt,
        final(krnl).pg_arr == old(krnl).pg_arr,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).ctn_mp == old(krnl).ctn_mp,
        final(krnl).sched_mp == old(krnl).sched_mp,
        final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
        final(krnl).prc_mp == old(krnl).prc_mp,
        final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
        final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
        final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
        final(krnl).cpu_tlb == old(krnl).cpu_tlb,
        final(krnl).iommu_tlb == old(krnl).iommu_tlb,
        final(krnl).rt_ctn == old(krnl).rt_ctn,
        final(krnl).dflt_pt == old(krnl).dflt_pt,
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
{
    proof {
        assert(krnl.thr_mp.perms_wf()) by { reveal(thread_perms_wf); };
        assert(krnl.ep_mp.perms_wf()) by { reveal(endpoint_perms_wf); };
        assert({
            &&& krnl.thr_mp.view().spec_index(receiver_thread_ptr).is_init()
            &&& krnl.thr_mp.view().spec_index(receiver_thread_ptr).addr() == receiver_thread_ptr
            &&& krnl.ep_mp.view().spec_index(payload_endpoint_ptr).is_init()
            &&& krnl.ep_mp.view().spec_index(payload_endpoint_ptr).addr() == payload_endpoint_ptr
            &&& krnl.thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.wf()
            &&& krnl.ep_mp.spec_index(payload_endpoint_ptr).inv()
        }) by { reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(endpoints_inv); };
        assert({
            &&& !krnl.ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view().contains((receiver_thread_ptr, target_endpoint_index))
            &&& krnl.ep_mp.spec_index(payload_endpoint_ptr).view().rf_counter < usize::MAX
        }) by {
            reveal(thread_endpoint_ref_counter_wf);
            endpoint_ref_counter_bounded(&*krnl, payload_endpoint_ptr);
        };
    }
    {
        let receiver_thread_mut = krnl.thr_mp.borrow_mut_typed(receiver_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(receiver_thread_lock_perm));
        receiver_thread_mut.endpoint_descriptors.set(target_endpoint_index, Some(payload_endpoint_ptr));
    } {
        let payload_endpoint_mut = krnl.ep_mp.borrow_mut_typed(payload_endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(lctx), Tracked(payload_endpoint_lock_perm));
        payload_endpoint_mut.rf_counter = payload_endpoint_mut.rf_counter + 1;
        payload_endpoint_mut.owning_threads = Ghost(payload_endpoint_mut.owning_threads.view().insert((receiver_thread_ptr, target_endpoint_index)));
    }

    proof {
        assert(krnl.subsystems_inv()) by {
            assert(thread_perms_wf(krnl.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
            assert(endpoint_perms_wf(krnl.ep_mp)) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(krnl.memory_management_inv()) by { thread_endpoint_no_change_imply_memory_management_inv(*old(krnl), *krnl); };
        assert(krnl.process_management_inv()) by {
            assert(thread_endpoint_reference_added(old(krnl).thr_mp, krnl.thr_mp, receiver_thread_ptr, payload_endpoint_ptr, target_endpoint_index)) by { thread_endpoint_reference_added_from_single_update(old(krnl).thr_mp, krnl.thr_mp, receiver_thread_ptr, payload_endpoint_ptr, target_endpoint_index); };
            assert(endpoint_reference_added(old(krnl).ep_mp, krnl.ep_mp, receiver_thread_ptr, payload_endpoint_ptr, target_endpoint_index)) by { endpoint_reference_added_from_single_update(old(krnl).ep_mp, krnl.ep_mp, receiver_thread_ptr, payload_endpoint_ptr, target_endpoint_index); };
            assert(thread_caller_callee_wf(krnl.thr_mp)) by { reveal(thread_endpoint_reference_added); reveal(thread_caller_callee_wf); };
            assert(container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)) by { reveal(endpoint_reference_added); reveal(container_endpoint_wf); };
            assert(thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_endpoint_reference_added); reveal(endpoint_reference_added); reveal(thread_endpoint_ref_counter_wf); };
            assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_queue_fields(old(krnl).thr_mp, krnl.thr_mp, old(krnl).ep_mp, krnl.ep_mp); };
            assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_thread_endpoint_wf); reveal(thread_endpoint_reference_added); reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); };
            assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by { reveal(thread_endpoint_reference_added); reveal(container_thread_scheduler_wf); };
            assert(container_thread_wf(krnl.ctn_mp, krnl.thr_mp)) by { reveal(thread_endpoint_reference_added); reveal(container_thread_wf); };
            assert(process_thread_wf(krnl.prc_mp, krnl.thr_mp)) by { reveal(thread_endpoint_reference_added); reveal(process_thread_wf); };
            assert(thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)) by { reveal(thread_endpoint_reference_added); reveal(thread_cpu_wf); };
        };
        assert({
            &&& typed_lock_maps_aligned(krnl, lctx)
            &&& krnl.thr_mp.lock_id_by_key(receiver_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(receiver_thread_ptr)
            &&& krnl.ep_mp.lock_id_by_key(payload_endpoint_ptr) == old(krnl).ep_mp.lock_id_by_key(payload_endpoint_ptr)
        }) by { lock_id_fields_eq_imply_eq(); };
    }
}

pub(super) fn ipc_begin_endpoint_transfer(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId,
    process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    channel_endpoint_ptr: RwLockEndpointPtr,
    peer_thread_ptr: RwLockThreadPtr,
    source_thread_ptr: RwLockThreadPtr,
    source_endpoint_index: EndpointIdx,
    payload_endpoint_ptr: RwLockEndpointPtr,
    cpu_lock_perm: Tracked<&LockPerm>,
    process_lock_perm: Tracked<&LockPerm>,
    current_thread_lock_perm: Tracked<&LockPerm>,
    channel_endpoint_lock_perm: Tracked<LockPerm>,
    peer_thread_lock_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        current_thread_ptr != peer_thread_ptr,
        source_thread_ptr == current_thread_ptr || source_thread_ptr == peer_thread_ptr,
        edp_idx_valid(source_endpoint_index),
        old(krnl).thr_mp.dom().contains(source_thread_ptr),
        old(krnl).thr_mp.spec_index(source_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(source_thread_ptr).view().endpoint_descriptors.view().spec_index(source_endpoint_index as int) == Some(payload_endpoint_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).wlocked_by(old(lctx)),
        old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        process_lock_perm.view().state() is WriteLock,
        process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(channel_endpoint_ptr),
        old(krnl).ep_mp.spec_index(channel_endpoint_ptr).wlocked_by(old(lctx)),
        channel_endpoint_lock_perm.view().state() is WriteLock,
        channel_endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        channel_endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(channel_endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).wlocked_by(old(lctx)),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload is Endpoint,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(channel_endpoint_ptr),
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.spec_index(channel_endpoint_ptr).view().queue.len() != 0,
        old(krnl).ep_mp.spec_index(channel_endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        old(lctx).base_lock_scope(set![cpu_id], Set::empty(), set![process_ptr], set![current_thread_ptr, peer_thread_ptr], set![channel_endpoint_ptr]),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), channel_endpoint_ptr, TypedLockMode::Write),
        cpu_objects_unlocked_except(old(krnl).cpu_arr, old(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(old(krnl).pg_arr, old(lctx).thread_id()),
        container_objects_unlocked(old(krnl).ctn_mp, old(lctx).thread_id()),
        process_objects_unlocked_except(old(krnl).prc_mp, old(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked_except(old(krnl).ep_mp, old(lctx).thread_id(), set![channel_endpoint_ptr]),
        pagetable_objects_unlocked(old(krnl).pt_mp, old(lctx).thread_id()),
        iommu_table_objects_unlocked(old(krnl).it_mp, old(lctx).thread_id()),
        scheduler_objects_unlocked(old(krnl).sched_mp, old(lctx).thread_id()),
        pcid_allocator_objects_unlocked(old(krnl).pcid_allc_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_4k_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).is_init(),
        final(krnl).thr_mp.dom().contains(peer_thread_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).is_init(),
        final(krnl).ep_mp.dom().contains(payload_endpoint_ptr),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).is_init(),
        final(krnl).ep_mp.lock_id_by_key(payload_endpoint_ptr).major == ENDPOINT_LOCK_MAJOR,
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr) == old(krnl).thr_mp.spec_index(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread(),
        cpu_lock_perm.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_lock_perm.view().lock_id() == final(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        current_thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        peer_thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(source_thread_ptr).view().endpoint_descriptors.wf(),
        final(krnl).thr_mp.spec_index(source_thread_ptr).view().endpoint_descriptors.view().spec_index(source_endpoint_index as int) == Some(payload_endpoint_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().owning_container,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(final(lctx)),
        final(krnl).prc_mp.spec_index(process_ptr).wlocked_by(final(lctx)),
        final(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(final(lctx)),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).wlocked_by(final(lctx)),
        final(lctx).base_lock_scope(set![cpu_id], Set::empty(), set![process_ptr], set![current_thread_ptr, peer_thread_ptr], Set::empty()),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        cpu_objects_unlocked_except(final(krnl).cpu_arr, final(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(final(krnl).pg_arr, final(lctx).thread_id()),
        container_objects_unlocked(final(krnl).ctn_mp, final(lctx).thread_id()),
        process_objects_unlocked_except(final(krnl).prc_mp, final(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked(final(krnl).ep_mp, final(lctx).thread_id()),
        pagetable_objects_unlocked(final(krnl).pt_mp, final(lctx).thread_id()),
        iommu_table_objects_unlocked(final(krnl).it_mp, final(lctx).thread_id()),
        scheduler_objects_unlocked(final(krnl).sched_mp, final(lctx).thread_id()),
        pcid_allocator_objects_unlocked(final(krnl).pcid_allc_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(final(krnl).allc_4k_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
{
    let ghost old_peer_thread_lock_id = krnl.thr_mp.lock_id_by_key(peer_thread_ptr);
    let tracked channel_endpoint_lock_perm = channel_endpoint_lock_perm.get();
    let (_, Tracked(endpoint_node_perm)) = ipc_dequeue_endpoint_waiter(&mut krnl.ep_mp, Tracked(&*lctx), channel_endpoint_ptr, peer_thread_ptr, Tracked(&channel_endpoint_lock_perm));
    proof {
        assert({
            let peer_node_addr = old(krnl).thr_mp
                .spec_index(peer_thread_ptr).view()
                .endpoint_linkedlist_node.addr();
            &&& old(krnl).ep_mp
                .spec_index(channel_endpoint_ptr).view()
                .queue.map().dom().contains(peer_node_addr)
            &&& old(krnl).ep_mp
                .spec_index(channel_endpoint_ptr).view()
                .queue.map().spec_index(peer_node_addr) == peer_thread_ptr
            &&& endpoint_node_perm.addr() == peer_node_addr
        }) by { reveal(thread_endpoint_queue_wf); reveal(endpoint_perms_wf); reveal(endpoints_inv); reveal(LinkedList::wf_map); };
    }
    ipc_move_endpoint_waiter_to_transit(&mut krnl.thr_mp, Tracked(&*lctx), peer_thread_ptr, current_thread_ptr, Tracked(endpoint_node_perm), peer_thread_lock_perm);

    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Thread(peer_thread_ptr), old_peer_thread_lock_id, krnl.thr_mp.lock_id_by_key(peer_thread_ptr));
        assert(krnl.subsystems_inv()) by {
            assert({
                &&& thread_perms_wf(krnl.thr_mp)
                &&& endpoint_perms_wf(krnl.ep_mp)
            }) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(endpoint_perms_wf); reveal(endpoints_inv); };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(krnl.memory_management_inv()) by { thread_endpoint_no_change_imply_memory_management_inv(*old(krnl), *krnl); };
        assert(krnl.process_management_inv()) by {
            assert({
                &&& container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)
                &&& thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)
                &&& thread_caller_callee_wf(krnl.thr_mp)
            }) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_caller_callee_wf); };
            assert({
                &&& container_scheduler_wf(krnl.ctn_mp, krnl.sched_mp)
                &&& container_thread_wf(krnl.ctn_mp, krnl.thr_mp)
                &&& process_thread_wf(krnl.prc_mp, krnl.thr_mp)
                &&& thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)
            }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(thread_cpu_wf); };
            assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by {
                seq_skip_lemma::<RwLockThreadPtr>();
                seq_remove_lemma_2::<RwLockThreadPtr>();
                reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(endpoints_inv); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_map); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf);
            };
            assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf); };
            assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
        };
        assert({
            &&& cpu_dirty_map_wf(krnl.ctn_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp)
            &&& tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr)
            &&& typed_lock_maps_aligned(krnl, &*lctx)
            &&& cpu_objects_unlocked_except(krnl.cpu_arr, lctx.thread_id(), set![cpu_id])
            &&& page_objects_unlocked(krnl.pg_arr, lctx.thread_id())
            &&& container_objects_unlocked(krnl.ctn_mp, lctx.thread_id())
            &&& process_objects_unlocked_except(krnl.prc_mp, lctx.thread_id(), set![process_ptr])
            &&& thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![current_thread_ptr, peer_thread_ptr])
            &&& endpoint_objects_unlocked_except(krnl.ep_mp, lctx.thread_id(), set![channel_endpoint_ptr])
            &&& pagetable_objects_unlocked(krnl.pt_mp, lctx.thread_id())
            &&& iommu_table_objects_unlocked(krnl.it_mp, lctx.thread_id())
            &&& scheduler_objects_unlocked(krnl.sched_mp, lctx.thread_id())
            &&& pcid_allocator_objects_unlocked(krnl.pcid_allc_mp, lctx.thread_id())
            &&& allocator_objects_unlocked(krnl.allc_4k_mp, lctx.thread_id())
            &&& allocator_objects_unlocked(krnl.allc_2m_mp, lctx.thread_id())
            &&& allocator_objects_unlocked(krnl.allc_1g_mp, lctx.thread_id())
        }) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); reveal(tlb_wf_spec); };
    }

    krnl.wunlock_endpoint(channel_endpoint_ptr, Tracked(&mut *lctx), Tracked(channel_endpoint_lock_perm));
    proof {
        krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
        assert({
            &&& krnl.thr_mp.spec_index(current_thread_ptr).is_init()
            &&& krnl.thr_mp.spec_index(peer_thread_ptr).is_init()
            &&& krnl.ep_mp.dom().contains(payload_endpoint_ptr)
            &&& krnl.ep_mp.spec_index(payload_endpoint_ptr).is_init()
            &&& krnl.ep_mp.lock_id_by_key(payload_endpoint_ptr).major == ENDPOINT_LOCK_MAJOR
        }) by { reveal(thread_perms_wf); reveal(thread_endpoint_ref_counter_wf); reveal(endpoint_perms_wf); reveal(endpoints_inv); };
    }
}

pub(super) fn ipc_finish_endpoint_transit(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId,
    process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    payload_endpoint_ptr: RwLockEndpointPtr,
    peer_thread_ptr: RwLockThreadPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr,
    result: RetValueType,
    cpu_lock_perm: Tracked<LockPerm>,
    process_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>,
    payload_endpoint_lock_perm: Tracked<LockPerm>,
    peer_thread_lock_perm: Tracked<LockPerm>,
    peer_scheduler_lock_perm: Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        current_thread_ptr != peer_thread_ptr,
        old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).wlocked_by(old(lctx)),
        old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        process_lock_perm.view().state() is WriteLock,
        process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(payload_endpoint_ptr),
        old(krnl).ep_mp.spec_index(payload_endpoint_ptr).wlocked_by(old(lctx)),
        payload_endpoint_lock_perm.view().state() is WriteLock,
        payload_endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        payload_endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).wlocked_by(old(lctx)),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(peer_scheduler_ptr),
        old(krnl).sched_mp.spec_index(peer_scheduler_ptr).wlocked_by(old(lctx)),
        peer_scheduler_lock_perm.view().state() is WriteLock,
        peer_scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(peer_scheduler_ptr).locking_thread()->Write_lock_id,
        {
            let peer_container = old(krnl).thr_mp
                .spec_index(peer_thread_ptr).view().owning_container;
            &&& old(krnl).ctn_mp.dom().contains(peer_container)
            &&& old(krnl).ctn_mp.spec_index(peer_container)
                .view_rodata().view().scheduler == peer_scheduler_ptr
            &&& old(krnl).sched_mp.spec_index(peer_scheduler_ptr)
                .view().owning_container == peer_container
        },
        !old(krnl).sched_mp.spec_index(peer_scheduler_ptr).view()
            .queue.view().contains(peer_thread_ptr),
        old(lctx).object_lock_scope(Set::empty(), set![cpu_id], Set::empty(), set![process_ptr], set![current_thread_ptr, peer_thread_ptr], set![payload_endpoint_ptr], set![peer_scheduler_ptr], Set::empty(), Set::empty(), Set::empty()),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), payload_endpoint_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), peer_scheduler_ptr, TypedLockMode::Write),
        cpu_objects_unlocked_except(old(krnl).cpu_arr, old(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(old(krnl).pg_arr, old(lctx).thread_id()),
        container_objects_unlocked(old(krnl).ctn_mp, old(lctx).thread_id()),
        process_objects_unlocked_except(old(krnl).prc_mp, old(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked_except(old(krnl).ep_mp, old(lctx).thread_id(), set![payload_endpoint_ptr]),
        pagetable_objects_unlocked(old(krnl).pt_mp, old(lctx).thread_id()),
        iommu_table_objects_unlocked(old(krnl).it_mp, old(lctx).thread_id()),
        scheduler_objects_unlocked_except(old(krnl).sched_mp, old(lctx).thread_id(), set![peer_scheduler_ptr]),
        pcid_allocator_objects_unlocked(old(krnl).pcid_allc_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_4k_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        ret == result,
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
{
    let ghost old_peer_thread_lock_id = krnl.thr_mp.lock_id_by_key(peer_thread_ptr);
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked process_lock_perm = process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked payload_endpoint_lock_perm = payload_endpoint_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();
    let tracked peer_scheduler_lock_perm = peer_scheduler_lock_perm.get();

    assert(krnl.sched_mp.spec_index(peer_scheduler_ptr).view().queue.length != usize::MAX) by { scheduler_queue_len_bounded(&*krnl, peer_scheduler_ptr); };
    let (scheduler_node_addr, scheduler_node_perm) = ipc_schedule_endpoint_transit(&mut krnl.thr_mp, Tracked(&*lctx), peer_thread_ptr, current_thread_ptr, result, Tracked(&peer_thread_lock_perm));
    ipc_enqueue_scheduled_thread(&mut krnl.sched_mp, Tracked(&*lctx), peer_scheduler_ptr, peer_thread_ptr, scheduler_node_addr, scheduler_node_perm, Tracked(&peer_scheduler_lock_perm));

    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Thread(peer_thread_ptr), old_peer_thread_lock_id, krnl.thr_mp.lock_id_by_key(peer_thread_ptr));
        assert(krnl.subsystems_inv()) by {
            assert({
                &&& thread_perms_wf(krnl.thr_mp)
                &&& endpoint_perms_wf(krnl.ep_mp)
                &&& scheduler_perms_wf(krnl.sched_mp)
            }) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(endpoint_perms_wf); reveal(endpoints_inv); reveal(scheduler_perms_wf); };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(krnl.memory_management_inv()) by { thread_endpoint_no_change_imply_memory_management_inv(*old(krnl), *krnl); };
        assert(krnl.process_management_inv()) by {
            assert({
                &&& container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)
                &&& thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)
                &&& thread_caller_callee_wf(krnl.thr_mp)
            }) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_caller_callee_wf); };
            assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(endpoints_inv); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); };
            assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_thread_endpoint_wf); };
            assert({
                &&& container_scheduler_wf(krnl.ctn_mp, krnl.sched_mp)
                &&& container_thread_wf(krnl.ctn_mp, krnl.thr_mp)
                &&& process_thread_wf(krnl.prc_mp, krnl.thr_mp)
                &&& thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)
            }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(thread_cpu_wf); };
            assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by {
                seq_push_lemma::<RwLockThreadPtr>();
                reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_map);
            };
        };
        assert({
            &&& cpu_dirty_map_wf(krnl.ctn_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp)
            &&& tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr)
            &&& typed_lock_maps_aligned(krnl, &*lctx)
            &&& cpu_objects_unlocked_except(krnl.cpu_arr, lctx.thread_id(), set![cpu_id])
            &&& page_objects_unlocked(krnl.pg_arr, lctx.thread_id())
            &&& container_objects_unlocked(krnl.ctn_mp, lctx.thread_id())
            &&& process_objects_unlocked_except(krnl.prc_mp, lctx.thread_id(), set![process_ptr])
            &&& thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![current_thread_ptr, peer_thread_ptr])
            &&& endpoint_objects_unlocked_except(krnl.ep_mp, lctx.thread_id(), set![payload_endpoint_ptr])
            &&& pagetable_objects_unlocked(krnl.pt_mp, lctx.thread_id())
            &&& iommu_table_objects_unlocked(krnl.it_mp, lctx.thread_id())
            &&& scheduler_objects_unlocked_except(krnl.sched_mp, lctx.thread_id(), set![peer_scheduler_ptr])
            &&& pcid_allocator_objects_unlocked(krnl.pcid_allc_mp, lctx.thread_id())
            &&& allocator_objects_unlocked(krnl.allc_4k_mp, lctx.thread_id())
            &&& allocator_objects_unlocked(krnl.allc_2m_mp, lctx.thread_id())
            &&& allocator_objects_unlocked(krnl.allc_1g_mp, lctx.thread_id())
        }) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); reveal(tlb_wf_spec); };
    }

    krnl.wunlock_thread(peer_thread_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm));
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    krnl.wunlock_scheduler(peer_scheduler_ptr, Tracked(&mut *lctx), Tracked(peer_scheduler_lock_perm));
    krnl.wunlock_endpoint(payload_endpoint_ptr, Tracked(&mut *lctx), Tracked(payload_endpoint_lock_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        steps.end_kernel_step(&*krnl, &*lctx);
    }
    result
}

pub(super) fn ipc_rendezvous_endpoint(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId,
    process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    channel_endpoint_ptr: RwLockEndpointPtr,
    peer_thread_ptr: RwLockThreadPtr,
    source_thread_ptr: RwLockThreadPtr,
    receiver_thread_ptr: RwLockThreadPtr,
    source_endpoint_index: EndpointIdx,
    target_endpoint_index: EndpointIdx,
    cpu_lock_perm: Tracked<LockPerm>,
    process_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>,
    channel_endpoint_lock_perm: Tracked<LockPerm>,
    peer_thread_lock_perm: Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        current_thread_ptr != peer_thread_ptr,
        source_thread_ptr == current_thread_ptr && receiver_thread_ptr == peer_thread_ptr || source_thread_ptr == peer_thread_ptr && receiver_thread_ptr == current_thread_ptr,
        edp_idx_valid(source_endpoint_index),
        edp_idx_valid(target_endpoint_index),
        old(krnl).thr_mp.dom().contains(source_thread_ptr),
        old(krnl).thr_mp.spec_index(source_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.dom().contains(receiver_thread_ptr),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).wlocked_by(old(lctx)),
        old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        process_lock_perm.view().state() is WriteLock,
        process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(channel_endpoint_ptr),
        old(krnl).ep_mp.spec_index(channel_endpoint_ptr).wlocked_by(old(lctx)),
        channel_endpoint_lock_perm.view().state() is WriteLock,
        channel_endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        channel_endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(channel_endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).wlocked_by(old(lctx)),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload is Endpoint,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(channel_endpoint_ptr),
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(lctx).base_lock_scope(set![cpu_id], Set::empty(), set![process_ptr], set![current_thread_ptr, peer_thread_ptr], set![channel_endpoint_ptr]),
        old(lctx).held_lock_majors_lt(SCHEDULER_LOCK_MAJOR),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), channel_endpoint_ptr, TypedLockMode::Write),
        old(krnl).ep_mp.spec_index(channel_endpoint_ptr).view().queue.len() != 0,
        old(krnl).ep_mp.spec_index(channel_endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        cpu_objects_unlocked_except(old(krnl).cpu_arr, old(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(old(krnl).pg_arr, old(lctx).thread_id()),
        container_objects_unlocked(old(krnl).ctn_mp, old(lctx).thread_id()),
        process_objects_unlocked_except(old(krnl).prc_mp, old(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked_except(old(krnl).ep_mp, old(lctx).thread_id(), set![channel_endpoint_ptr]),
        pagetable_objects_unlocked(old(krnl).pt_mp, old(lctx).thread_id()),
        iommu_table_objects_unlocked(old(krnl).it_mp, old(lctx).thread_id()),
        scheduler_objects_unlocked(old(krnl).sched_mp, old(lctx).thread_id()),
        pcid_allocator_objects_unlocked(old(krnl).pcid_allc_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_4k_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        ret is Success || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch,
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked process_lock_perm = process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked channel_endpoint_lock_perm = channel_endpoint_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();

    proof {
        assert({
            &&& krnl.thr_mp.perms_wf()
            &&& krnl.thr_mp.spec_index(current_thread_ptr).is_init()
            &&& krnl.thr_mp.spec_index(peer_thread_ptr).is_init()
        }) by { reveal(thread_perms_wf); };
    }
    let source_endpoint_option = if source_thread_ptr == current_thread_ptr {
        *krnl.thr_mp.borrow(current_thread_ptr, Tracked(&current_thread_lock_perm)).endpoint_descriptors.get(source_endpoint_index)
    } else {
        *krnl.thr_mp.borrow(peer_thread_ptr, Tracked(&peer_thread_lock_perm)).endpoint_descriptors.get(source_endpoint_index)
    };
    let target_endpoint_option = if receiver_thread_ptr == current_thread_ptr {
        *krnl.thr_mp.borrow(current_thread_ptr, Tracked(&current_thread_lock_perm)).endpoint_descriptors.get(target_endpoint_index)
    } else {
        *krnl.thr_mp.borrow(peer_thread_ptr, Tracked(&peer_thread_lock_perm)).endpoint_descriptors.get(target_endpoint_index)
    };
    if let None = source_endpoint_option {
        return ipc_schedule_waiting_peer_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, channel_endpoint_ptr, peer_thread_ptr, RetValueType::ErrorIpcEndpointSourceInvalid, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(channel_endpoint_lock_perm), Tracked(peer_thread_lock_perm));
    }
    if let Some(_) = target_endpoint_option {
        return ipc_schedule_waiting_peer_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, channel_endpoint_ptr, peer_thread_ptr, RetValueType::ErrorIpcEndpointTargetInUse, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(channel_endpoint_lock_perm), Tracked(peer_thread_lock_perm));
    }
    let payload_endpoint_ptr = source_endpoint_option.unwrap();

    ipc_begin_endpoint_transfer(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, channel_endpoint_ptr, peer_thread_ptr, source_thread_ptr, source_endpoint_index, payload_endpoint_ptr, Tracked(&cpu_lock_perm), Tracked(&process_lock_perm), Tracked(&current_thread_lock_perm), Tracked(channel_endpoint_lock_perm), Tracked(&peer_thread_lock_perm));

    proof {
        assert({
            &&& !krnl.ep_mp.spec_index(payload_endpoint_ptr)
                .locked_by_thread(lctx.thread_id())
        }) by { reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf); };
    }
    let Tracked(payload_endpoint_lock_perm) = krnl.wlock_endpoint(payload_endpoint_ptr, Tracked(&mut *lctx));
    proof {
        assert({
            &&& krnl.ep_mp.perms_wf()
            &&& krnl.thr_mp.perms_wf()
        }) by { reveal(endpoint_perms_wf); reveal(thread_perms_wf); };
    }
    let payload_endpoint_ref = krnl.ep_mp.borrow(payload_endpoint_ptr, Tracked(&payload_endpoint_lock_perm));
    let endpoint_owner = payload_endpoint_ref.owning_container;
    let receiver_container = if receiver_thread_ptr == current_thread_ptr {
        krnl.thr_mp.borrow(current_thread_ptr, Tracked(&current_thread_lock_perm)).owning_container
    } else {
        krnl.thr_mp.borrow(peer_thread_ptr, Tracked(&peer_thread_lock_perm)).owning_container
    };
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(endpoint_owner)
            &&& krnl.ctn_mp.dom().contains(receiver_container)
            &&& container_perms_wf(krnl.ctn_mp)
            &&& container_tree_wf(krnl.rt_ctn, krnl.ctn_mp)
        }) by { reveal(container_endpoint_wf); reveal(container_thread_wf); };
    }
    let owner_compatible = if endpoint_owner == receiver_container {
        true
    } else {
        container_tree_check_is_ancestor(krnl.rt_ctn, &krnl.ctn_mp, endpoint_owner, receiver_container)
    };
    let result = if owner_compatible {
        if receiver_thread_ptr == current_thread_ptr {
            ipc_copy_endpoint_reference(krnl, receiver_thread_ptr, target_endpoint_index, payload_endpoint_ptr, Tracked(&*lctx), Tracked(&current_thread_lock_perm), Tracked(&payload_endpoint_lock_perm));
        } else {
            ipc_copy_endpoint_reference(krnl, receiver_thread_ptr, target_endpoint_index, payload_endpoint_ptr, Tracked(&*lctx), Tracked(&peer_thread_lock_perm), Tracked(&payload_endpoint_lock_perm));
        }
        RetValueType::Success
    } else {
        RetValueType::ErrorIpcEndpointOwnerMismatch
    };

    proof {
        assert(
            krnl.thr_mp.perms_wf()
                && krnl.thr_mp.spec_index(peer_thread_ptr).is_init()
        ) by { reveal(thread_perms_wf); };
    }
    let peer_container_ptr = krnl.thr_mp.borrow(peer_thread_ptr, Tracked(&peer_thread_lock_perm)).owning_container;
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(peer_container_ptr)
            &&& krnl.ctn_mp.view().spec_index(peer_container_ptr)
                .is_init()
            &&& krnl.ctn_mp.view().spec_index(peer_container_ptr)
                .addr() == peer_container_ptr
        }) by { reveal(container_perms_wf); reveal(container_thread_wf); };
    }
    let peer_scheduler_ptr = krnl.ctn_mp
        .borrow_rodata(peer_container_ptr).borrow().scheduler;
    proof {
        assert({
            &&& krnl.sched_mp.dom().contains(peer_scheduler_ptr)
            &&& !krnl.sched_mp.spec_index(peer_scheduler_ptr)
                .locked_by_thread(lctx.thread_id())
        }) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(scheduler_perms_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf); };
    }
    let Tracked(peer_scheduler_lock_perm) = krnl.wlock_scheduler(peer_scheduler_ptr, Tracked(&mut *lctx));
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(peer_container_ptr)
            &&& krnl.ctn_mp.spec_index(peer_container_ptr)
                .view_rodata().view().scheduler == peer_scheduler_ptr
            &&& krnl.sched_mp.spec_index(peer_scheduler_ptr).view()
                .owning_container == peer_container_ptr
            &&& !krnl.sched_mp.spec_index(peer_scheduler_ptr).view()
                .queue.view().contains(peer_thread_ptr)
        }) by { reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
    }
    ipc_finish_endpoint_transit(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, payload_endpoint_ptr, peer_thread_ptr, peer_scheduler_ptr, result, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(payload_endpoint_lock_perm), Tracked(peer_thread_lock_perm), Tracked(peer_scheduler_lock_perm))
}

}
