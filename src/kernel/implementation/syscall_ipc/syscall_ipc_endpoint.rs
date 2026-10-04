use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_queue::{
    ipc_dequeue_endpoint_waiter, ipc_enqueue_scheduled_thread, ipc_move_endpoint_waiter_to_transit,
    ipc_schedule_endpoint_transit,
};
use super::syscall_ipc_transition::ipc_schedule_waiting_peer_and_finish;
use super::syscall_ipc_dispatch::running_thread_not_in_endpoint_queue;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
#[verifier::spinoff_prover]
pub(super) fn ipc_copy_endpoint_reference(krnl: &mut KernelK, receiver_thread_ptr: RwLockThreadPtr, target_endpoint_index: EndpointIdx, payload_endpoint_ptr: RwLockEndpointPtr, Tracked(lctx): Tracked<&LocalContext>, Tracked(receiver_thread_lock_perm): Tracked<&LockPerm>, Tracked(payload_endpoint_lock_perm): Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        lctx.kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), lctx),
        old(krnl).thr_mp.dom().contains(receiver_thread_ptr),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).is_init(),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), receiver_thread_ptr, TypedLockMode::Write),
        receiver_thread_lock_perm.state() is WriteLock,
        receiver_thread_lock_perm.thread_id() == lctx.thread_id(),
        receiver_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(receiver_thread_ptr).locking_thread()->Write_lock_id,
        edp_idx_valid(target_endpoint_index),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.spec_index(target_endpoint_index) is None,
        old(krnl).ep_mp.dom().contains(payload_endpoint_ptr),
        old(krnl).ep_mp.spec_index(payload_endpoint_ptr).is_init(),
        typed_lock_map_contains_mode(lctx.endpoint_lock_map(), payload_endpoint_ptr, TypedLockMode::Write),
        payload_endpoint_lock_perm.state() is WriteLock,
        payload_endpoint_lock_perm.thread_id() == lctx.thread_id(),
        payload_endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).locking_thread()->Write_lock_id,
        {
            let endpoint_owner = old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_container;
            &&& old(krnl).ctn_mp.dom().contains(endpoint_owner)
            &&& {
                let receiver_container = old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().owning_container;
                ||| endpoint_owner == receiver_container
                ||| old(krnl).ctn_mp.spec_index(endpoint_owner).view_ghost().subtree_set.view().contains(receiver_container)
            }
        },
    ensures
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view() == (Thread {
            endpoint_descriptors: final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors,
            ..old(krnl).thr_mp.spec_index(receiver_thread_ptr).view()
        }),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, receiver_thread_ptr),
        final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, payload_endpoint_ptr),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), receiver_thread_ptr, TypedLockMode::Write),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(receiver_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().state == old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().syscall_progress == old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().syscall_progress,
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(receiver_thread_ptr).view()),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_4k == old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_4k,
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_2m,
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().temp_alloc_cache_1g,
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(receiver_thread_ptr).locking_thread(),
        final(krnl).thr_mp.lock_id_by_key(receiver_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(receiver_thread_ptr),
        typed_lock_map_contains_mode(lctx.endpoint_lock_map(), payload_endpoint_ptr, TypedLockMode::Write),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).locking_thread() == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).locking_thread(),
        final(krnl).ep_mp.lock_id_by_key(payload_endpoint_ptr) == old(krnl).ep_mp.lock_id_by_key(payload_endpoint_ptr),
        final(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view() =~= old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view().update(target_endpoint_index as int, Some(payload_endpoint_ptr)),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view() =~= old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view().insert((receiver_thread_ptr, target_endpoint_index)),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().rf_counter == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().rf_counter + 1,
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().queue.view() == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().queue.view(),
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().queue_state == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().queue_state,
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_container == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_container,
        final(krnl).ep_mp.spec_index(payload_endpoint_ptr).being_killed() == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).being_killed(),
        *final(krnl) == (KernelK {
            thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp,
            ..*old(krnl)
        }),
        kernel_k_to_nonlock_kernel_u(*final(krnl)).thread_map.spec_index(receiver_thread_ptr) == (ThreadU {
            endpoint_descriptors: kernel_k_to_nonlock_kernel_u(*old(krnl)).thread_map.spec_index(receiver_thread_ptr).endpoint_descriptors.update(target_endpoint_index as int, Some(payload_endpoint_ptr)),
            ..kernel_k_to_nonlock_kernel_u(*old(krnl)).thread_map.spec_index(receiver_thread_ptr)
        }),
{
    hide(Seq::contains);
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
        }) by { reveal(thread_perms_wf); reveal(endpoint_perms_wf); };
        assert({
            &&& !krnl.ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view().contains((receiver_thread_ptr, target_endpoint_index))
            &&& krnl.ep_mp.spec_index(payload_endpoint_ptr).view().rf_counter < usize::MAX
        }) by { reveal(thread_endpoint_ref_counter_wf); endpoint_ref_counter_bounded(&*krnl, payload_endpoint_ptr); };
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
            assert(thread_perms_wf(krnl.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); };
            assert(endpoint_perms_wf(krnl.ep_mp)) by { reveal(endpoint_perms_wf); };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(krnl.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(*old(krnl), *krnl); };
        assert(krnl.process_management_inv()) by {
            assert(thread_caller_callee_wf(krnl.thr_mp)) by { reveal(thread_caller_callee_wf); };
            assert(container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); };
            assert(thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_perms_wf); reveal(thread_endpoint_ref_counter_wf); };
            assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_queue_fields(old(krnl).thr_mp, krnl.thr_mp, old(krnl).ep_mp, krnl.ep_mp); };
            assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_thread_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); };
            assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by { reveal(container_thread_scheduler_wf); };
            assert(container_thread_wf(krnl.ctn_mp, krnl.thr_mp)) by { reveal(container_thread_wf); };
            assert(process_thread_wf(krnl.prc_mp, krnl.thr_mp)) by { reveal(process_thread_wf); };
            assert(thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)) by { reveal(thread_cpu_wf); };
        };
        assert({
            &&& typed_lock_maps_aligned(krnl, lctx)
            &&& krnl.thr_mp.lock_id_by_key(receiver_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(receiver_thread_ptr)
            &&& krnl.ep_mp.lock_id_by_key(payload_endpoint_ptr) == old(krnl).ep_mp.lock_id_by_key(payload_endpoint_ptr)
        }) by { lock_id_fields_eq_imply_eq(); };
        assert(kernel_k_to_nonlock_kernel_u(*krnl).thread_map.spec_index(receiver_thread_ptr) == (ThreadU {
            endpoint_descriptors: kernel_k_to_nonlock_kernel_u(*old(krnl)).thread_map.spec_index(receiver_thread_ptr).endpoint_descriptors.update(target_endpoint_index as int, Some(payload_endpoint_ptr)),
            ..kernel_k_to_nonlock_kernel_u(*old(krnl)).thread_map.spec_index(receiver_thread_ptr)
        })) by { kernel_thread_nonlock_projection_at(old(krnl), receiver_thread_ptr); kernel_thread_nonlock_projection_at(&*krnl, receiver_thread_ptr); };
    }
}

#[verifier::spinoff_prover]
pub(super) fn ipc_begin_endpoint_transfer(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, channel_endpoint_ptr: RwLockEndpointPtr,
    peer_thread_ptr: RwLockThreadPtr, source_thread_ptr: RwLockThreadPtr, source_endpoint_index: EndpointIdx,
    payload_endpoint_ptr: RwLockEndpointPtr, channel_endpoint_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<&LockPerm>,
    peer_thread_lock_perm: Tracked<&LockPerm>, Ghost(channel_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>,
    Ghost(payload_index): Ghost<EndpointIdx>,
)
    requires
        old(krnl).inv(),
        forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
            old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
            old(steps).snapshot_k().thr_mp.dom().contains(p) && old(krnl).thr_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
            old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
            old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
            old(steps).snapshot_k().it_mp.dom().contains(p) && old(krnl).it_mp.dom().contains(p) ==> if old(lctx).iommu_table_lock_map().dom().contains(p) {
                old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if old(lctx).cpu_lock_map().dom().contains(i) {
                old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
            } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        ipc_endpoint_transit_step_pre(old(steps).snapshot_u(), cpu_id, channel_index, waiting_state, payload_index),
        old(steps).snapshot_u().cpu_array[cpu_id as int].current_process == Some(process_ptr),
        old(steps).snapshot_u().cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr),
        old(steps).snapshot_u().thread_map[current_thread_ptr].endpoint_descriptors[channel_index as int] == Some(channel_endpoint_ptr),
        old(steps).snapshot_u().endpoint_map[channel_endpoint_ptr].queue[0] == peer_thread_ptr,
        current_thread_ptr != peer_thread_ptr,
        source_thread_ptr == current_thread_ptr || source_thread_ptr == peer_thread_ptr,
        edp_idx_valid(source_endpoint_index),
        old(krnl).thr_mp.dom().contains(source_thread_ptr),
        old(krnl).thr_mp.spec_index(source_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(source_thread_ptr).view().endpoint_descriptors.view().spec_index(source_endpoint_index as int) == Some(payload_endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).prc_mp.dom().contains(process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(channel_endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), channel_endpoint_ptr, TypedLockMode::Write),
        channel_endpoint_lock_perm.view().state() is WriteLock,
        channel_endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        channel_endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(channel_endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload is Endpoint,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(channel_endpoint_ptr),
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.spec_index(channel_endpoint_ptr).view().queue.len() != 0,
        old(krnl).ep_mp.spec_index(channel_endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![channel_endpoint_ptr],
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
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(steps).view().len() == old(steps).view().len() + 1,
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ipc_endpoint_trace_after_transit(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), old(steps).snapshot_u(), cpu_id, channel_index,
            waiting_state, payload_index),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).nonlock_snapshot_u().thread_map.dom().contains(peer_thread_ptr),
        final(steps).nonlock_snapshot_u().thread_map.spec_index(peer_thread_ptr).state is IPC_ENDPOINT_TRANSIT,
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
        final(krnl).thr_mp.spec_index(current_thread_ptr).view() == (Thread {
            syscall_progress: final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(current_thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IpcEndpoint { peer: peer_thread_ptr, caller_sends: waiting_state is SENDING, payload_index }),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread(),
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
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        final(lctx).container_lock_map().dom().is_empty(),
        final(lctx).process_lock_map().dom() =~= set![process_ptr],
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        final(lctx).endpoint_lock_map().dom().is_empty(),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
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
        typed_lock_maps_aligned(final(krnl), final(lctx)),
{
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };

    let ghost old_peer_thread_lock_id = krnl.thr_mp.lock_id_by_key(peer_thread_ptr);
    let tracked channel_endpoint_lock_perm = channel_endpoint_lock_perm.get();
    let (_, Tracked(endpoint_node_perm)) = ipc_dequeue_endpoint_waiter(&mut krnl.ep_mp, Tracked(&*lctx), channel_endpoint_ptr, peer_thread_ptr, Tracked(&channel_endpoint_lock_perm));
    proof {
        assert({
            let peer_node_addr = old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_linkedlist_node.addr();
            &&& old(krnl).ep_mp.spec_index(channel_endpoint_ptr).view().queue.map().dom().contains(peer_node_addr)
            &&& old(krnl).ep_mp.spec_index(channel_endpoint_ptr).view().queue.map().spec_index(peer_node_addr) == peer_thread_ptr
            &&& endpoint_node_perm.addr() == peer_node_addr
        }) by { reveal(thread_endpoint_queue_wf); reveal(endpoint_perms_wf); reveal(LinkedList::wf_map); };
    }
    ipc_move_endpoint_waiter_to_transit(&mut krnl.thr_mp, Tracked(&*lctx), peer_thread_ptr, current_thread_ptr, Tracked(endpoint_node_perm), peer_thread_lock_perm);

    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Thread(peer_thread_ptr), old_peer_thread_lock_id, krnl.thr_mp.lock_id_by_key(peer_thread_ptr));
        assert(krnl.subsystems_inv()) by {
            assert({
                &&& thread_perms_wf(krnl.thr_mp)
                &&& endpoint_perms_wf(krnl.ep_mp)
            }) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(endpoint_perms_wf); };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(krnl.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(*old(krnl), *krnl); };
        assert(krnl.process_management_inv()) by {
            assert({
                &&& container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)
                &&& thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)
                &&& thread_caller_callee_wf(krnl.thr_mp)
            }) by { reveal(thread_perms_wf); reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_caller_callee_wf); };
            assert({
                &&& container_scheduler_wf(krnl.ctn_mp, krnl.sched_mp)
                &&& container_thread_wf(krnl.ctn_mp, krnl.thr_mp)
                &&& process_thread_wf(krnl.prc_mp, krnl.thr_mp)
                &&& thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)
            }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(thread_cpu_wf); };
            assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by {
                seq_skip_lemma::<RwLockThreadPtr>();
                lemma_seq_remove_value_membership::<RwLockThreadPtr>();
                reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_map); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf);
            };
            assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf); };
            assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
        };
        assert({
            &&& cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)
            &&& tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)
            &&& typed_lock_maps_aligned(krnl, &*lctx)
        }) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); reveal(tlb_wf_spec); };
    }

    krnl.wunlock_endpoint(channel_endpoint_ptr, Tracked(&mut *lctx), Tracked(channel_endpoint_lock_perm));
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(Some(SyscallProgress::IpcEndpoint { peer: peer_thread_ptr, caller_sends: waiting_state is SENDING, payload_index })),
        Tracked(&*lctx), current_thread_lock_perm);
    proof {
        assert(kernel_thread_state_changed(&steps.snapshot_k(), &*krnl, peer_thread_ptr)) by { reveal(kernel_thread_state_changed); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); };
        assert(steps.snapshot_k().thr_mp.dom().contains(peer_thread_ptr) && krnl.thr_mp.dom().contains(peer_thread_ptr)) by { reveal(kernel_thread_state_changed); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); };
        use_type_invariant(&*steps);
        assert(steps.snapshot_u() != kernel_k_to_kernel_u(*krnl)
            && ipc_endpoint_transit_step(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, channel_index, waiting_state, payload_index)) by {
            kernel_thread_dequeued_and_locks_changed_implies_u_step(&steps.snapshot_k(), old(krnl), &*krnl, &*lctx,
                cpu_id, process_ptr, current_thread_ptr, peer_thread_ptr, channel_endpoint_ptr);
            ipc_endpoint_transit_step_from_u(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, current_thread_ptr, channel_endpoint_ptr, peer_thread_ptr, channel_index, waiting_state, payload_index);
        };
        let ghost old_state = steps.snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().state;
        let ghost new_state = krnl.thr_mp.spec_index(peer_thread_ptr).view().state;
        let ghost transit_k = *krnl;
        krnl.kernel_step_boundary_thread_state_changed(&mut *lctx, &mut *steps, peer_thread_ptr, old_state, new_state,);
        assert(ipc_endpoint_trace_after_transit(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), old(steps).snapshot_u(), cpu_id, channel_index, waiting_state, payload_index)) by {
            ipc_endpoint_trace_transit_step(&*steps, old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(transit_k), cpu_id, channel_index, waiting_state, payload_index);
        };
        assert({
            &&& krnl.thr_mp.spec_index(current_thread_ptr).is_init()
            &&& krnl.thr_mp.spec_index(peer_thread_ptr).is_init()
            &&& krnl.ep_mp.dom().contains(payload_endpoint_ptr)
            &&& krnl.ep_mp.spec_index(payload_endpoint_ptr).is_init()
            &&& krnl.ep_mp.lock_id_by_key(payload_endpoint_ptr).major == ENDPOINT_LOCK_MAJOR
        }) by { reveal(thread_perms_wf); reveal(thread_endpoint_ref_counter_wf); reveal(endpoint_perms_wf); };
    }
}

#[verifier::spinoff_prover]
pub(super) fn ipc_finish_endpoint_transit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, payload_endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    peer_scheduler_ptr: RwLockSchedulerPtr, result: RetValueType, cpu_lock_perm: Tracked<LockPerm>, process_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>, payload_endpoint_lock_perm: Tracked<LockPerm>, Ghost(receiver_thread_ptr): Ghost<RwLockThreadPtr>,
    Ghost(target_endpoint_index): Ghost<EndpointIdx>, Ghost(source_endpoint_index): Ghost<EndpointIdx>, peer_thread_lock_perm: Tracked<LockPerm>,
    peer_scheduler_lock_perm: Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        ipc_endpoint_finish_step_pre(old(steps).snapshot_u(), cpu_id),
        receiver_thread_ptr == current_thread_ptr || receiver_thread_ptr == peer_thread_ptr,
        edp_idx_valid(target_endpoint_index),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(steps).snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().ipc_payload
            == (IPCPayLoad::Endpoint { endpoint_index: if receiver_thread_ptr == peer_thread_ptr { target_endpoint_index } else { source_endpoint_index } }),
        old(steps).snapshot_k().thr_mp.spec_index(if receiver_thread_ptr == peer_thread_ptr { current_thread_ptr } else { peer_thread_ptr }).view().endpoint_descriptors.view()[source_endpoint_index as int]
            == Some(payload_endpoint_ptr),
        {
            let owner = old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().owning_container;
            let container = old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).view().owning_container;
            &&& old(steps).snapshot_k().ctn_mp.dom().contains(container)
            &&& result == if owner == container || old(steps).snapshot_k().ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(owner) {
                RetValueType::Success
            } else { RetValueType::ErrorIpcEndpointOwnerMismatch }
        },
        *old(krnl) == (KernelK { thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, sched_mp: old(krnl).sched_mp, ..old(steps).snapshot_k() }),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, receiver_thread_ptr),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).locking_thread(),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).being_killed() == old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).view() == (Thread {
            endpoint_descriptors: old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors,
            ..old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).view()
        }),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view() == if result is Success {
            old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view().update(target_endpoint_index as int, Some(payload_endpoint_ptr))
        } else { old(steps).snapshot_k().thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.view() },
        old(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, payload_endpoint_ptr),
        old(krnl).ep_mp.spec_index(payload_endpoint_ptr).being_killed() == old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).being_killed(),
        old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().queue.view() == old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().queue.view(),
        old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().queue_state == old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().queue_state,
        old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_container == old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().owning_container,
        old(krnl).ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view() == if result is Success {
            old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view().insert((receiver_thread_ptr, target_endpoint_index))
        } else { old(steps).snapshot_k().ep_mp.spec_index(payload_endpoint_ptr).view().owning_threads.view() },
        old(krnl).sched_mp.dom() == old(steps).snapshot_k().sched_mp.dom(),
        forall|p: RwLockSchedulerPtr| #![trigger old(krnl).sched_mp.spec_index(p)]
            old(krnl).sched_mp.dom().contains(p) ==> old(krnl).sched_mp.spec_index(p).view().queue.view() == old(steps).snapshot_k().sched_mp.spec_index(p).view().queue.view(),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k().thr_mp.dom().contains(peer_thread_ptr),
        old(steps).snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT,
        current_thread_ptr != peer_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0,
        process_lock_perm.view().state() is WriteLock,
        process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
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
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(payload_endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), payload_endpoint_ptr, TypedLockMode::Write),
        payload_endpoint_lock_perm.view().state() is WriteLock,
        payload_endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        payload_endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(payload_endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(peer_scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), peer_scheduler_ptr, TypedLockMode::Write),
        peer_scheduler_lock_perm.view().state() is WriteLock,
        peer_scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(peer_scheduler_ptr).locking_thread()->Write_lock_id,
        {
            let peer_container = old(krnl).thr_mp.spec_index(peer_thread_ptr).view().owning_container;
            &&& old(krnl).ctn_mp.dom().contains(peer_container)
            &&& old(krnl).ctn_mp.spec_index(peer_container).view_rodata().view().scheduler == peer_scheduler_ptr
            &&& old(krnl).sched_mp.spec_index(peer_scheduler_ptr).view().owning_container == peer_container
        },
        !old(krnl).sched_mp.spec_index(peer_scheduler_ptr).view().queue.view().contains(peer_thread_ptr),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![payload_endpoint_ptr],
        old(lctx).scheduler_lock_map().dom() =~= set![peer_scheduler_ptr],
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
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
        ipc_endpoint_finish_step(old(steps).snapshot_u(), kernel_k_to_kernel_u(*final(krnl)), cpu_id),
        result == ipc_endpoint_finish_result(old(steps).snapshot_u(), cpu_id),
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
            }) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(endpoint_perms_wf); reveal(scheduler_perms_wf); };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(krnl.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(*old(krnl), *krnl); };
        assert(krnl.process_management_inv()) by {
            assert({
                &&& container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)
                &&& thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)
                &&& thread_caller_callee_wf(krnl.thr_mp)
            }) by { reveal(thread_perms_wf); reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_caller_callee_wf); };
            assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); };
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
            &&& cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)
            &&& tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)
            &&& typed_lock_maps_aligned(krnl, &*lctx)
        }) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); reveal(tlb_wf_spec); };
    }

    krnl.wunlock_thread(peer_thread_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm));
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    krnl.wunlock_scheduler(peer_scheduler_ptr, Tracked(&mut *lctx), Tracked(peer_scheduler_lock_perm));
    krnl.wunlock_endpoint(payload_endpoint_ptr, Tracked(&mut *lctx), Tracked(payload_endpoint_lock_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert(kernel_thread_state_changed(&steps.snapshot_k(), &*krnl, peer_thread_ptr)) by { reveal(kernel_thread_state_changed); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); };
        assert(steps.snapshot_k().thr_mp.dom().contains(peer_thread_ptr) && krnl.thr_mp.dom().contains(peer_thread_ptr)) by { reveal(kernel_thread_state_changed); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); };
        use_type_invariant(&*steps);
        assert(steps.snapshot_u() != kernel_k_to_kernel_u(*krnl) && ipc_endpoint_finish_step(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id)
            && result == ipc_endpoint_finish_result(steps.snapshot_u(), cpu_id)) by {
            reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
            kernel_peer_scheduled_and_locks_released_implies_u_step(&steps.snapshot_k(), &*krnl, cpu_id, process_ptr,
                current_thread_ptr, peer_thread_ptr, payload_endpoint_ptr, result, false,
                if result is Success { Some((receiver_thread_ptr, target_endpoint_index)) } else { None });
            kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, current_thread_ptr, Some(payload_endpoint_ptr));
            kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, peer_thread_ptr, None);
            kernel_container_ancestry_projection_at(&steps.snapshot_k(), steps.snapshot_k().thr_mp.spec_index(receiver_thread_ptr).view().owning_container);
            ipc_endpoint_finish_step_from_u(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, current_thread_ptr, peer_thread_ptr, payload_endpoint_ptr, receiver_thread_ptr,
                source_endpoint_index, target_endpoint_index, result, if result is Success { Some((receiver_thread_ptr, target_endpoint_index)) } else { None });
        };
        let ghost old_state = steps.snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().state;
        let ghost new_state = krnl.thr_mp.spec_index(peer_thread_ptr).view().state;
        steps.end_kernel_step_thread_state_changed(&*krnl, &*lctx, peer_thread_ptr, old_state, new_state,);
    }
    result
}

#[verifier::spinoff_prover]
pub(super) fn ipc_rendezvous_endpoint(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, channel_endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    source_thread_ptr: RwLockThreadPtr, receiver_thread_ptr: RwLockThreadPtr, source_endpoint_index: EndpointIdx, target_endpoint_index: EndpointIdx,
    cpu_lock_perm: Tracked<LockPerm>, process_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>,
    channel_endpoint_lock_perm: Tracked<LockPerm>, Ghost(channel_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>,
    peer_thread_lock_perm: Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        edp_idx_valid(channel_index),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[channel_index as int] == Some(channel_endpoint_ptr),
        waiting_state is SENDING || waiting_state is RECEIVING,
        (old(krnl).ep_mp.spec_index(channel_endpoint_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
        forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
            old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
            old(steps).snapshot_k().thr_mp.dom().contains(p) && old(krnl).thr_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
            old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
            old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
            old(steps).snapshot_k().it_mp.dom().contains(p) && old(krnl).it_mp.dom().contains(p) ==> if old(lctx).iommu_table_lock_map().dom().contains(p) {
                old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if old(lctx).cpu_lock_map().dom().contains(i) {
                old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
            } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
        current_thread_ptr != peer_thread_ptr,
        source_thread_ptr == (if waiting_state is SENDING { current_thread_ptr } else { peer_thread_ptr }),
        receiver_thread_ptr == (if waiting_state is SENDING { peer_thread_ptr } else { current_thread_ptr }),
        edp_idx_valid(source_endpoint_index),
        edp_idx_valid(target_endpoint_index),
        old(krnl).thr_mp.dom().contains(source_thread_ptr),
        old(krnl).thr_mp.spec_index(source_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.dom().contains(receiver_thread_ptr),
        old(krnl).thr_mp.spec_index(receiver_thread_ptr).view().endpoint_descriptors.wf(),
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
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(channel_endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), channel_endpoint_ptr, TypedLockMode::Write),
        channel_endpoint_lock_perm.view().state() is WriteLock,
        channel_endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        channel_endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(channel_endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == (if waiting_state is SENDING { ThreadState::RECEIVING } else { ThreadState::SENDING }),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload
            == (IPCPayLoad::Endpoint { endpoint_index: if waiting_state is SENDING { target_endpoint_index } else { source_endpoint_index } }),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(channel_endpoint_ptr),
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![channel_endpoint_ptr],
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
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(krnl).ep_mp.spec_index(channel_endpoint_ptr).view().queue.len() != 0,
        old(krnl).ep_mp.spec_index(channel_endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ipc_endpoint_rendezvous_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, channel_index, waiting_state, if waiting_state is SENDING { source_endpoint_index } else { target_endpoint_index }, ret),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret is Success || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch,
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        ret is Success || ret is ErrorIpcEndpointOwnerMismatch ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 2,
        ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
{
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };

    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked process_lock_perm = process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked channel_endpoint_lock_perm = channel_endpoint_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();

    proof { thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr); }
    let source_endpoint_option = if source_thread_ptr == current_thread_ptr {
        *krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm)).endpoint_descriptors.get(source_endpoint_index)
    } else {
        *krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm)).endpoint_descriptors.get(source_endpoint_index)
    };
    let target_endpoint_option = if receiver_thread_ptr == current_thread_ptr {
        *krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm)).endpoint_descriptors.get(target_endpoint_index)
    } else {
        *krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm)).endpoint_descriptors.get(target_endpoint_index)
    };
    let ghost payload = IPCPayLoad::Endpoint { endpoint_index: if waiting_state is SENDING { source_endpoint_index } else { target_endpoint_index } };
    proof {
        assert({
            let pre = kernel_k_to_kernel_u(steps.snapshot_k());
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr)
            &&& pre.endpoint_map[channel_endpoint_ptr].queue[0] == peer_thread_ptr
            &&& pre.thread_map[current_thread_ptr].endpoint_descriptors == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()
            &&& pre.thread_map[peer_thread_ptr].endpoint_descriptors == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_descriptors.view()
            &&& pre.thread_map[peer_thread_ptr].state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state
            &&& pre.thread_map[peer_thread_ptr].ipc_payload == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload
        }) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
            kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, current_thread_ptr, Some(channel_endpoint_ptr));
            kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, peer_thread_ptr, None);
        };
    }
    let payload_endpoint_ptr = match source_endpoint_option {
        Some(payload_endpoint_ptr) => payload_endpoint_ptr,
        None => {
            proof { use_type_invariant(&*steps); assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
            let ret = ipc_schedule_waiting_peer_and_finish(
                krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, channel_endpoint_ptr, Ghost(Some((channel_index, waiting_state, payload))),
                peer_thread_ptr, RetValueType::ErrorIpcEndpointSourceInvalid, Tracked(cpu_lock_perm), Tracked(process_lock_perm),
                Tracked(current_thread_lock_perm), Tracked(channel_endpoint_lock_perm), Tracked(peer_thread_lock_perm),
            );
            proof { ipc_rendezvous_trace_error_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, channel_index, waiting_state, payload, ret); }
            return ret;
        },
    };
    if target_endpoint_option.is_some() {
        proof { use_type_invariant(&*steps); assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        let ret = ipc_schedule_waiting_peer_and_finish(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, channel_endpoint_ptr, Ghost(Some((channel_index, waiting_state, payload))),
            peer_thread_ptr, RetValueType::ErrorIpcEndpointTargetInUse, Tracked(cpu_lock_perm), Tracked(process_lock_perm),
            Tracked(current_thread_lock_perm), Tracked(channel_endpoint_lock_perm), Tracked(peer_thread_lock_perm),
        );
        proof { ipc_rendezvous_trace_error_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, channel_index, waiting_state, payload, ret); }
        return ret;
    }

    let ghost payload_index = if waiting_state is SENDING { source_endpoint_index } else { target_endpoint_index };
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        running_thread_not_in_endpoint_queue(&*krnl, channel_endpoint_ptr, current_thread_ptr);
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, peer_thread_ptr);
        use_type_invariant(&*steps);
        assert({
            let pre = steps.snapshot_u();
            &&& pre.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr)
            &&& pre.thread_map[current_thread_ptr].endpoint_descriptors[channel_index as int] == Some(channel_endpoint_ptr)
            &&& pre.endpoint_map[channel_endpoint_ptr].queue[0] == peer_thread_ptr
            &&& ipc_endpoint_transit_step_pre(pre, cpu_id, channel_index, waiting_state, payload_index)
        }) by {
            container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, current_thread_ptr);
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, current_thread_ptr, Some(channel_endpoint_ptr));
            kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, peer_thread_ptr, None);
            ipc_endpoint_transit_step_pre_from_u(steps.snapshot_u(), cpu_id, process_ptr, current_thread_ptr, channel_endpoint_ptr, peer_thread_ptr, channel_index, waiting_state,
                source_endpoint_index, target_endpoint_index);
        };
    }
    ipc_begin_endpoint_transfer(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, channel_endpoint_ptr, peer_thread_ptr, source_thread_ptr,
        source_endpoint_index, payload_endpoint_ptr, Tracked(channel_endpoint_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&peer_thread_lock_perm),
        Ghost(channel_index), Ghost(waiting_state), Ghost(payload_index),
    );

    proof {
        assert(!lctx.endpoint_lock_map().dom().contains(payload_endpoint_ptr)) by { vstd::set::axiom_set_ext_equal(lctx.endpoint_lock_map().dom(), Set::empty()); };
        use_type_invariant(&*steps);
        assert({
            let u = steps.snapshot_u();
            &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& u.process_map.dom().contains(process_ptr)
            &&& u.process_map[process_ptr].lock_state is WriteLocked
            &&& u.thread_map.dom().contains(current_thread_ptr)
            &&& u.thread_map[current_thread_ptr].lock_state is WriteLocked
            &&& u.thread_map.dom().contains(peer_thread_ptr)
            &&& u.thread_map[peer_thread_ptr].lock_state is WriteLocked
        }) by {
            kernel_write_held_context_projection(&*krnl, &*lctx, cpu_id, process_ptr, current_thread_ptr, None);
            kernel_write_held_context_projection(&*krnl, &*lctx, cpu_id, process_ptr, peer_thread_ptr, None);
        };
    }
    let Tracked(payload_endpoint_lock_perm) = krnl.wlock_endpoint(payload_endpoint_ptr, Tracked(&mut *lctx));
    proof {
        use_type_invariant(&*steps);
        assert(ipc_endpoint_finish_step_pre(steps.snapshot_u(), cpu_id)) by {
            container_thread_wf_at(steps.snapshot_k().ctn_mp, steps.snapshot_k().thr_mp, current_thread_ptr);
            container_thread_wf_at(steps.snapshot_k().ctn_mp, steps.snapshot_k().thr_mp, peer_thread_ptr);
            kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, current_thread_ptr, Some(payload_endpoint_ptr));
            kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, peer_thread_ptr, None);
            ipc_endpoint_finish_step_pre_from_u(steps.snapshot_u(), cpu_id, process_ptr, current_thread_ptr, peer_thread_ptr, payload_endpoint_ptr, receiver_thread_ptr,
                source_endpoint_index, target_endpoint_index);
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };

        endpoint_perms_wf_at(krnl.ep_mp, payload_endpoint_ptr); thread_perms_wf_at(krnl.thr_mp, current_thread_ptr);
    }
    let payload_endpoint_ref = krnl.ep_mp.borrow_typed(payload_endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&payload_endpoint_lock_perm));
    let endpoint_owner = payload_endpoint_ref.owning_container;
    let receiver_container = if receiver_thread_ptr == current_thread_ptr {
        krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm)).owning_container
    } else {
        krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm)).owning_container
    };
    proof { container_endpoint_wf_at(krnl.ctn_mp, krnl.ep_mp, payload_endpoint_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, receiver_thread_ptr); }
    let owner_compatible = if endpoint_owner == receiver_container {
        true
    } else {
        container_tree_check_is_ancestor(krnl.rt_ctn, &krnl.ctn_mp, endpoint_owner, receiver_container)
    };
    proof {
        use_type_invariant(&*steps);
        assert(steps.snapshot_u().thread_map[source_thread_ptr].endpoint_descriptors[source_endpoint_index as int] == Some(payload_endpoint_ptr)) by {
            kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, source_thread_ptr, None);
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
        };
    }
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

    proof { thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr); }
    let peer_container_ptr = krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm)).owning_container;
    proof { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, peer_thread_ptr); container_perms_wf_at(krnl.ctn_mp, peer_container_ptr); }
    let peer_scheduler_ptr = krnl.ctn_mp.borrow_rodata(peer_container_ptr).borrow().scheduler;
    proof { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, peer_container_ptr); }
    let Tracked(peer_scheduler_lock_perm) = krnl.wlock_scheduler(peer_scheduler_ptr, Tracked(&mut *lctx));
    proof {
        container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, peer_container_ptr);
        container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, peer_scheduler_ptr, peer_thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread_ptr);
    }
    let ghost finish_before = steps.view();
    let ghost finish_pre_u = steps.snapshot_u();
    let ret = ipc_finish_endpoint_transit(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, payload_endpoint_ptr, peer_thread_ptr, peer_scheduler_ptr,
        result, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(payload_endpoint_lock_perm),
        Ghost(receiver_thread_ptr), Ghost(target_endpoint_index), Ghost(source_endpoint_index), Tracked(peer_thread_lock_perm), Tracked(peer_scheduler_lock_perm),
    );
    proof {
        ipc_endpoint_trace_finish_step(&*steps, finish_before, old(steps).view().len() as int, kernel_k_to_kernel_u(old(steps).snapshot_k()), finish_pre_u, kernel_k_to_kernel_u(*krnl), cpu_id, channel_index, waiting_state, payload_index, ret);
    }
    ret
}
}
