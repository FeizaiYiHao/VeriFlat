use vstd::prelude::*;
use vstd::assert_sets_equal;

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
    kernel: &mut KernelK,
    receiver_thread_ptr: RwLockThreadPtr,
    target_endpoint_index: EndpointIdx,
    payload_endpoint_ptr: RwLockEndpointPtr,
    Tracked(lctx): Tracked<&LocalContext>,
    Tracked(receiver_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(payload_endpoint_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(kernel).inv(),
        lctx.kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(kernel), lctx),
        old(kernel).thread_map.dom().contains(receiver_thread_ptr),
        old(kernel).thread_map.spec_index(receiver_thread_ptr).is_init(),
        old(kernel).thread_map.spec_index(receiver_thread_ptr)
            .wlocked_by(lctx),
        receiver_thread_lock_perm.state() is WriteLock,
        receiver_thread_lock_perm.thread_id() == lctx.thread_id(),
        receiver_thread_lock_perm.lock_id()
            == old(kernel).thread_map.spec_index(receiver_thread_ptr)
                .locking_thread()->Write_lock_id,
        edp_idx_valid(target_endpoint_index),
        old(kernel).thread_map.spec_index(receiver_thread_ptr).view()
            .endpoint_descriptors.wf(),
        old(kernel).thread_map.spec_index(receiver_thread_ptr).view()
            .endpoint_descriptors.spec_index(target_endpoint_index) is None,
        old(kernel).endpoint_map.dom().contains(payload_endpoint_ptr),
        old(kernel).endpoint_map.spec_index(payload_endpoint_ptr).is_init(),
        old(kernel).endpoint_map.spec_index(payload_endpoint_ptr)
            .wlocked_by(lctx),
        payload_endpoint_lock_perm.state() is WriteLock,
        payload_endpoint_lock_perm.thread_id() == lctx.thread_id(),
        payload_endpoint_lock_perm.lock_id()
            == old(kernel).endpoint_map.spec_index(payload_endpoint_ptr)
                .locking_thread()->Write_lock_id,
        {
            let endpoint_owner = old(kernel).endpoint_map
                .spec_index(payload_endpoint_ptr).view().owning_container;
            &&& old(kernel).container_map.dom().contains(endpoint_owner)
            &&& {
            let receiver_container = old(kernel).thread_map
                .spec_index(receiver_thread_ptr).view().owning_container;
            ||| endpoint_owner == receiver_container
            ||| old(kernel).container_map.spec_index(endpoint_owner).view()
                .subtree_set.view().contains(receiver_container)
            }
        },
    ensures
        final(kernel).inv(),
        typed_lock_maps_aligned(final(kernel), lctx),
        final(kernel).thread_map.unchanged_except(
            &old(kernel).thread_map, receiver_thread_ptr),
        final(kernel).endpoint_map.unchanged_except(
            &old(kernel).endpoint_map, payload_endpoint_ptr),
        final(kernel).thread_map.spec_index(receiver_thread_ptr)
            .wlocked_by(lctx),
        final(kernel).thread_map.spec_index(receiver_thread_ptr)
            .being_killed()
            == old(kernel).thread_map.spec_index(receiver_thread_ptr)
                .being_killed(),
        final(kernel).thread_map.spec_index(receiver_thread_ptr).view().state
            == old(kernel).thread_map.spec_index(receiver_thread_ptr).view()
                .state,
        final(kernel).thread_map.spec_index(receiver_thread_ptr).view()
            .free_quota_pending_fields_equal(
                &old(kernel).thread_map.spec_index(receiver_thread_ptr).view()),
        final(kernel).thread_map.spec_index(receiver_thread_ptr).view()
            .temp_alloc_cache_4k
            == old(kernel).thread_map.spec_index(receiver_thread_ptr).view()
                .temp_alloc_cache_4k,
        final(kernel).thread_map.spec_index(receiver_thread_ptr).view()
            .temp_alloc_cache_2m
            == old(kernel).thread_map.spec_index(receiver_thread_ptr).view()
                .temp_alloc_cache_2m,
        final(kernel).thread_map.spec_index(receiver_thread_ptr).view()
            .temp_alloc_cache_1g
            == old(kernel).thread_map.spec_index(receiver_thread_ptr).view()
                .temp_alloc_cache_1g,
        final(kernel).thread_map.spec_index(receiver_thread_ptr)
            .locking_thread()
            == old(kernel).thread_map.spec_index(receiver_thread_ptr)
                .locking_thread(),
        final(kernel).thread_map.lock_id_by_key(receiver_thread_ptr)
            == old(kernel).thread_map.lock_id_by_key(receiver_thread_ptr),
        final(kernel).endpoint_map.spec_index(payload_endpoint_ptr)
            .wlocked_by(lctx),
        final(kernel).endpoint_map.spec_index(payload_endpoint_ptr)
            .locking_thread()
            == old(kernel).endpoint_map.spec_index(payload_endpoint_ptr)
                .locking_thread(),
        final(kernel).endpoint_map.lock_id_by_key(payload_endpoint_ptr)
            == old(kernel).endpoint_map.lock_id_by_key(payload_endpoint_ptr),
        final(kernel).thread_map.spec_index(receiver_thread_ptr).view()
            .endpoint_descriptors.view()
            =~= old(kernel).thread_map.spec_index(receiver_thread_ptr).view()
                .endpoint_descriptors.view().update(
                    target_endpoint_index as int,
                    Some(payload_endpoint_ptr),
                ),
        final(kernel).endpoint_map.spec_index(payload_endpoint_ptr).view()
            .owning_threads.view()
            =~= old(kernel).endpoint_map.spec_index(payload_endpoint_ptr).view()
                .owning_threads.view().insert(
                    (receiver_thread_ptr, target_endpoint_index),
                ),
        final(kernel).endpoint_map.spec_index(payload_endpoint_ptr).view()
            .rf_counter
            == old(kernel).endpoint_map.spec_index(payload_endpoint_ptr).view()
                .rf_counter + 1,
        final(kernel).pagetable_map == old(kernel).pagetable_map,
        final(kernel).iommu_table_map == old(kernel).iommu_table_map,
        final(kernel).iommu_root_table == old(kernel).iommu_root_table,
        final(kernel).page_array == old(kernel).page_array,
        final(kernel).cpu_array == old(kernel).cpu_array,
        final(kernel).container_map == old(kernel).container_map,
        final(kernel).scheduler_map == old(kernel).scheduler_map,
        final(kernel).pcid_allocator_map == old(kernel).pcid_allocator_map,
        final(kernel).process_map == old(kernel).process_map,
        final(kernel).allocator_4k_map == old(kernel).allocator_4k_map,
        final(kernel).allocator_2m_map == old(kernel).allocator_2m_map,
        final(kernel).allocator_1g_map == old(kernel).allocator_1g_map,
        final(kernel).cpu_tlb == old(kernel).cpu_tlb,
        final(kernel).iommu_tlb == old(kernel).iommu_tlb,
        final(kernel).root_container == old(kernel).root_container,
        final(kernel).default_pagetable == old(kernel).default_pagetable,
        kernel_k_to_kernel_u(*final(kernel)) == kernel_k_to_kernel_u(*old(kernel)),
{
    proof {
        assert({
            &&& kernel.thread_map.perms_wf()
            &&& kernel.endpoint_map.perms_wf()
            &&& kernel.thread_map.spec_index(receiver_thread_ptr).view()
                .endpoint_descriptors.wf()
            &&& kernel.endpoint_map.spec_index(payload_endpoint_ptr).inv()
        }) by {
            reveal(thread_perms_wf);
            reveal(endpoint_perms_wf);
            reveal(endpoints_inv);
        };
        assert(!kernel.endpoint_map.spec_index(payload_endpoint_ptr).view()
            .owning_threads.view().contains(
                (receiver_thread_ptr, target_endpoint_index),
            )) by {
            reveal(thread_endpoint_ref_counter_wf);
        };
        assert(kernel.endpoint_map.spec_index(payload_endpoint_ptr).view()
            .rf_counter < usize::MAX) by {
            endpoint_ref_counter_bounded(&*kernel, payload_endpoint_ptr);
        };
    }
    {
        let receiver_thread_mut = kernel.thread_map.borrow_mut(
            receiver_thread_ptr,
            Tracked(lctx),
            Tracked(receiver_thread_lock_perm),
        );
        receiver_thread_mut.endpoint_descriptors.set(
            target_endpoint_index,
            Some(payload_endpoint_ptr),
        );
    }
    {
        let payload_endpoint_mut = kernel.endpoint_map.borrow_mut(
            payload_endpoint_ptr,
            Tracked(lctx),
            Tracked(payload_endpoint_lock_perm),
        );
        payload_endpoint_mut.rf_counter = payload_endpoint_mut.rf_counter + 1;
        payload_endpoint_mut.owning_threads = Ghost(
            payload_endpoint_mut.owning_threads.view().insert(
                (receiver_thread_ptr, target_endpoint_index),
            ),
        );
    }

    proof {
        assert(kernel.subsystems_inv()) by {
            assert(thread_perms_wf(kernel.thread_map)) by {
                reveal(thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
                reveal(thread_temp_alloc_empty_unless_wlocked);
            };
            assert(endpoint_perms_wf(kernel.endpoint_map)) by {
                reveal(endpoint_perms_wf);
                reveal(endpoints_inv);
            };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(kernel.memory_management_inv()) by {
            assert(thread_pages_wf(kernel.thread_map, kernel.page_array)) by {
                reveal(thread_pages_wf);
            };
            assert(thread_staged_pages_wf(
                kernel.thread_map, kernel.page_array,
            )) by {
                thread_staged_pages_4k_wf_preserved_for_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
                thread_staged_pages_2m_wf_preserved_for_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
                thread_staged_pages_1g_wf_preserved_for_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
            };
            assert(endpoint_pages_wf(
                kernel.endpoint_map, kernel.page_array,
            )) by {
                reveal(endpoint_pages_wf);
            };
            assert(container_process_allocator_quota_wf(
                kernel.container_map, kernel.process_map, kernel.thread_map,
                kernel.allocator_4k_map, kernel.allocator_2m_map,
                kernel.allocator_1g_map,
            )) by {
                reveal(thread_quota_4k_fields_unchanged);
                reveal(thread_quota_2m_fields_unchanged);
                reveal(thread_quota_1g_fields_unchanged);
                container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields_forall();
                container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields_forall();
                container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields_forall();
            };
        };
        assert(kernel.process_management_inv()) by {
            reveal(KernelK::process_management_inv);
            thread_endpoint_reference_added_from_single_update(
                old(kernel).thread_map, kernel.thread_map,
                receiver_thread_ptr, payload_endpoint_ptr,
                target_endpoint_index,
            );
            endpoint_reference_added_from_single_update(
                old(kernel).endpoint_map, kernel.endpoint_map,
                receiver_thread_ptr, payload_endpoint_ptr,
                target_endpoint_index,
            );
            assert(thread_caller_callee_wf(kernel.thread_map)) by {
                reveal(thread_endpoint_reference_added);
                reveal(thread_caller_callee_wf);
            };
            assert(container_endpoint_wf(
                kernel.container_map, kernel.endpoint_map,
            )) by {
                reveal(endpoint_reference_added);
                reveal(container_endpoint_wf);
            };
            assert(thread_endpoint_ref_counter_wf(
                kernel.thread_map, kernel.endpoint_map,
            )) by {
                reveal(thread_endpoint_reference_added);
                reveal(endpoint_reference_added);
                reveal(thread_endpoint_ref_counter_wf);
            };
            assert(thread_endpoint_queue_wf(
                kernel.thread_map, kernel.endpoint_map,
            )) by {
                reveal(thread_endpoint_queue_fields_unchanged);
                reveal(endpoint_queue_fields_unchanged);
                thread_endpoint_queue_wf_preserved_for_queue_fields(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).endpoint_map, kernel.endpoint_map,
                );
            };
            assert(container_thread_endpoint_wf(
                kernel.container_map, kernel.thread_map, kernel.endpoint_map,
            )) by {
                reveal(endpoint_owning_container_fields_unchanged);
                container_thread_endpoint_wf_preserved_on_reference_add(
                    kernel.container_map,
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).endpoint_map, kernel.endpoint_map,
                    receiver_thread_ptr, payload_endpoint_ptr,
                    target_endpoint_index,
                );
            };
            assert(container_thread_scheduler_wf(
                kernel.container_map, kernel.thread_map, kernel.scheduler_map,
            )) by {
                reveal(thread_endpoint_reference_added);
                reveal(container_thread_scheduler_wf);
            };
            assert(container_thread_wf(
                kernel.container_map, kernel.thread_map,
            )) by {
                reveal(thread_endpoint_reference_added);
                reveal(container_thread_wf);
            };
            assert(process_thread_wf(
                kernel.process_map, kernel.thread_map,
            )) by {
                reveal(thread_endpoint_reference_added);
                reveal(process_thread_wf);
            };
            assert(thread_cpu_wf(
                kernel.thread_map, kernel.cpu_array,
            )) by {
                reveal(thread_endpoint_reference_added);
                reveal(thread_cpu_wf);
            };
        };
        assert(kernel.endpoint_map.lock_id_by_key(payload_endpoint_ptr)
            == old(kernel).endpoint_map.lock_id_by_key(payload_endpoint_ptr)) by {
            lock_id_fields_eq_imply_eq();
        };
        assert(kernel.thread_map.lock_id_by_key(receiver_thread_ptr)
            == old(kernel).thread_map.lock_id_by_key(receiver_thread_ptr)) by {
            lock_id_fields_eq_imply_eq();
        };
        assert(typed_lock_maps_aligned(kernel, lctx)) by {
            reveal(typed_lock_maps_aligned);
        };
        assert(kernel_k_to_kernel_u(*kernel)
            == kernel_k_to_kernel_u(*old(kernel))) by {
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                old(kernel), kernel,
            );
        };
    }
}

pub(super) fn ipc_begin_endpoint_transfer(
    kernel: &mut KernelK,
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
        old(kernel).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
        current_thread_ptr != peer_thread_ptr,
        source_thread_ptr == current_thread_ptr
            || source_thread_ptr == peer_thread_ptr,
        edp_idx_valid(source_endpoint_index),
        old(kernel).thread_map.dom().contains(source_thread_ptr),
        old(kernel).thread_map.spec_index(source_thread_ptr).view()
            .endpoint_descriptors.wf(),
        old(kernel).thread_map.spec_index(source_thread_ptr).view()
            .endpoint_descriptors.view().spec_index(source_endpoint_index as int)
            == Some(payload_endpoint_ptr),
        old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(kernel).cpu_array.spec_index(cpu_id).view().being_killed()
            == false,
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id()
            == old(kernel).cpu_array.spec_index(cpu_id).view()
                .locking_thread()->Write_lock_id,
        old(kernel).process_map.dom().contains(process_ptr),
        old(kernel).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
        old(kernel).process_map.spec_index(process_ptr).being_killed() == false,
        process_lock_perm.view().state() is WriteLock,
        process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        process_lock_perm.view().lock_id()
            == old(kernel).process_map.spec_index(process_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).thread_map.dom().contains(current_thread_ptr),
        old(kernel).thread_map.spec_index(current_thread_ptr)
            .wlocked_by(old(lctx)),
        old(kernel).thread_map.spec_index(current_thread_ptr).view().state
            == (ThreadState::RUNNING { cpu_id }),
        old(kernel).thread_map.spec_index(current_thread_ptr)
            .being_killed() == false,
        old(kernel).thread_map.spec_index(current_thread_ptr).view()
            .free_quota_pending_clean(),
        old(kernel).thread_map.spec_index(current_thread_ptr).view()
            .temp_alloc_clean(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id()
            == old(kernel).thread_map.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).endpoint_map.dom().contains(channel_endpoint_ptr),
        old(kernel).endpoint_map.spec_index(channel_endpoint_ptr)
            .wlocked_by(old(lctx)),
        channel_endpoint_lock_perm.view().state() is WriteLock,
        channel_endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        channel_endpoint_lock_perm.view().lock_id()
            == old(kernel).endpoint_map.spec_index(channel_endpoint_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).thread_map.dom().contains(peer_thread_ptr),
        old(kernel).thread_map.spec_index(peer_thread_ptr)
            .wlocked_by(old(lctx)),
        old(kernel).thread_map.spec_index(peer_thread_ptr)
            .being_killed() == false,
        old(kernel).thread_map.spec_index(peer_thread_ptr).view().state
            is SENDING
            || old(kernel).thread_map.spec_index(peer_thread_ptr).view().state
                is RECEIVING,
        old(kernel).thread_map.spec_index(peer_thread_ptr).view().ipc_payload
            is Endpoint,
        old(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .free_quota_pending_clean(),
        old(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .temp_alloc_clean(),
        old(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .blocking_endpoint_ptr == Some(channel_endpoint_ptr),
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id()
            == old(kernel).thread_map.spec_index(peer_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).endpoint_map.spec_index(channel_endpoint_ptr).view()
            .queue.len() != 0,
        old(kernel).endpoint_map.spec_index(channel_endpoint_ptr).view()
            .queue.view().spec_index(0) == peer_thread_ptr,
        cpu_objects_unlocked_except(
            old(kernel).cpu_array, old(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(old(kernel).page_array, old(lctx).thread_id()),
        container_objects_unlocked(
            old(kernel).container_map, old(lctx).thread_id()),
        process_objects_unlocked_except(
            old(kernel).process_map, old(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(
            old(kernel).thread_map, old(lctx).thread_id(),
            set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked_except(
            old(kernel).endpoint_map, old(lctx).thread_id(),
            set![channel_endpoint_ptr]),
        pagetable_objects_unlocked(
            old(kernel).pagetable_map, old(lctx).thread_id()),
        iommu_table_objects_unlocked(
            old(kernel).iommu_table_map, old(lctx).thread_id()),
        scheduler_objects_unlocked(
            old(kernel).scheduler_map, old(lctx).thread_id()),
        pcid_allocator_objects_unlocked(
            old(kernel).pcid_allocator_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_4k_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_2m_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_1g_map, old(lctx).thread_id()),
        typed_lock_maps_aligned(old(kernel), old(lctx)),
    ensures
        final(kernel).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
        final(kernel).thread_map.perms_wf(),
        final(kernel).endpoint_map.perms_wf(),
        final(kernel).container_map.perms_wf(),
        final(kernel).process_map.dom().contains(process_ptr),
        final(kernel).thread_map.dom().contains(current_thread_ptr),
        final(kernel).thread_map.spec_index(current_thread_ptr).is_init(),
        final(kernel).thread_map.dom().contains(peer_thread_ptr),
        final(kernel).thread_map.spec_index(peer_thread_ptr).is_init(),
        final(kernel).endpoint_map.dom().contains(payload_endpoint_ptr),
        final(kernel).endpoint_map.spec_index(payload_endpoint_ptr).is_init(),
        final(kernel).endpoint_map.lock_id_by_key(payload_endpoint_ptr).major
            == ENDPOINT_LOCK_MAJOR,
        final(kernel).cpu_array.spec_index(cpu_id)
            == old(kernel).cpu_array.spec_index(cpu_id),
        final(kernel).process_map.spec_index(process_ptr)
            == old(kernel).process_map.spec_index(process_ptr),
        final(kernel).thread_map.spec_index(current_thread_ptr)
            == old(kernel).thread_map.spec_index(current_thread_ptr),
        final(kernel).thread_map.spec_index(current_thread_ptr).view()
            .free_quota_pending_clean(),
        final(kernel).thread_map.spec_index(current_thread_ptr).view()
            .temp_alloc_clean(),
        final(kernel).thread_map.spec_index(peer_thread_ptr).locking_thread()
            == old(kernel).thread_map.spec_index(peer_thread_ptr)
                .locking_thread(),
        cpu_lock_perm.view().lock_id()
            == final(kernel).cpu_array.spec_index(cpu_id).view()
                .locking_thread()->Write_lock_id,
        process_lock_perm.view().lock_id()
            == final(kernel).process_map.spec_index(process_ptr)
                .locking_thread()->Write_lock_id,
        current_thread_lock_perm.view().lock_id()
            == final(kernel).thread_map.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        peer_thread_lock_perm.view().lock_id()
            == final(kernel).thread_map.spec_index(peer_thread_ptr)
                .locking_thread()->Write_lock_id,
        final(kernel).thread_map.spec_index(source_thread_ptr).view()
            .endpoint_descriptors.wf(),
        final(kernel).thread_map.spec_index(source_thread_ptr).view()
            .endpoint_descriptors.view().spec_index(source_endpoint_index as int)
            == Some(payload_endpoint_ptr),
        final(kernel).thread_map.spec_index(peer_thread_ptr).view().state
            is IPC_ENDPOINT_TRANSIT,
        final(kernel).thread_map.spec_index(peer_thread_ptr).view().ipc_payload
            == old(kernel).thread_map.spec_index(peer_thread_ptr).view()
                .ipc_payload,
        final(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .endpoint_descriptors.view()
            == old(kernel).thread_map.spec_index(peer_thread_ptr).view()
                .endpoint_descriptors.view(),
        final(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .owning_container
            == old(kernel).thread_map.spec_index(peer_thread_ptr).view()
                .owning_container,
        final(kernel).thread_map.spec_index(peer_thread_ptr)
            .being_killed() == false,
        final(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .free_quota_pending_clean(),
        final(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .temp_alloc_clean(),
        final(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(final(lctx)),
        final(kernel).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
        final(kernel).thread_map.spec_index(current_thread_ptr)
            .wlocked_by(final(lctx)),
        final(kernel).thread_map.spec_index(peer_thread_ptr)
            .wlocked_by(final(lctx)),
        cpu_objects_unlocked_except(
            final(kernel).cpu_array, final(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(final(kernel).page_array, final(lctx).thread_id()),
        container_objects_unlocked(
            final(kernel).container_map, final(lctx).thread_id()),
        process_objects_unlocked_except(
            final(kernel).process_map, final(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(
            final(kernel).thread_map, final(lctx).thread_id(),
            set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked(
            final(kernel).endpoint_map, final(lctx).thread_id()),
        pagetable_objects_unlocked(
            final(kernel).pagetable_map, final(lctx).thread_id()),
        iommu_table_objects_unlocked(
            final(kernel).iommu_table_map, final(lctx).thread_id()),
        scheduler_objects_unlocked(
            final(kernel).scheduler_map, final(lctx).thread_id()),
        pcid_allocator_objects_unlocked(
            final(kernel).pcid_allocator_map, final(lctx).thread_id()),
        allocator_objects_unlocked(
            final(kernel).allocator_4k_map, final(lctx).thread_id()),
        allocator_objects_unlocked(
            final(kernel).allocator_2m_map, final(lctx).thread_id()),
        allocator_objects_unlocked(
            final(kernel).allocator_1g_map, final(lctx).thread_id()),
        typed_lock_maps_aligned(final(kernel), final(lctx)),
{
    let ghost old_peer_thread_lock_id =
        kernel.thread_map.lock_id_by_key(peer_thread_ptr);
    let tracked channel_endpoint_lock_perm =
        channel_endpoint_lock_perm.get();
    let (_, Tracked(endpoint_node_perm)) =
        ipc_dequeue_endpoint_waiter(
            &mut kernel.endpoint_map, Tracked(&*lctx),
            channel_endpoint_ptr, peer_thread_ptr,
            Tracked(&channel_endpoint_lock_perm),
        );
    proof {
        assert({
            let peer_node_addr = old(kernel).thread_map
                .spec_index(peer_thread_ptr).view()
                .endpoint_linkedlist_node.addr();
            &&& old(kernel).endpoint_map
                .spec_index(channel_endpoint_ptr).view()
                .queue.map().dom().contains(peer_node_addr)
            &&& old(kernel).endpoint_map
                .spec_index(channel_endpoint_ptr).view()
                .queue.map().spec_index(peer_node_addr) == peer_thread_ptr
            &&& endpoint_node_perm.addr() == peer_node_addr
        }) by {
            reveal(thread_endpoint_queue_wf);
            reveal(endpoint_perms_wf);
            reveal(endpoints_inv);
            reveal(LinkedList::wf_map);
        };
    }
    ipc_move_endpoint_waiter_to_transit(
        &mut kernel.thread_map, Tracked(&*lctx),
        peer_thread_ptr, current_thread_ptr,
        Tracked(endpoint_node_perm), peer_thread_lock_perm,
    );

    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(
            KernelObjId::Thread(peer_thread_ptr),
            TypedHeldLock {
                lock_id: old_peer_thread_lock_id,
                mode: TypedLockMode::Write,
            },
            kernel.thread_map.lock_id_by_key(peer_thread_ptr),
        );
        assert(kernel.subsystems_inv()) by {
            assert({
                &&& thread_perms_wf(kernel.thread_map)
                &&& endpoint_perms_wf(kernel.endpoint_map)
            }) by {
                reveal(thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
                reveal(thread_temp_alloc_empty_unless_wlocked);
                reveal(endpoint_perms_wf);
                reveal(endpoints_inv);
            };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(kernel.memory_management_inv()) by {
            assert({
                &&& thread_quota_4k_fields_unchanged(
                    old(kernel).thread_map, kernel.thread_map)
                &&& thread_quota_2m_fields_unchanged(
                    old(kernel).thread_map, kernel.thread_map)
                &&& thread_quota_1g_fields_unchanged(
                    old(kernel).thread_map, kernel.thread_map)
            }) by {
                reveal(thread_quota_4k_fields_unchanged);
                reveal(thread_quota_2m_fields_unchanged);
                reveal(thread_quota_1g_fields_unchanged);
            };
            assert({
                &&& thread_pages_wf(kernel.thread_map, kernel.page_array)
                &&& endpoint_pages_wf(kernel.endpoint_map, kernel.page_array)
            }) by {
                reveal(thread_pages_wf);
                reveal(endpoint_pages_wf);
            };
            assert(thread_staged_pages_wf(
                kernel.thread_map, kernel.page_array,
            )) by {
                thread_staged_pages_4k_wf_preserved_for_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
                thread_staged_pages_2m_wf_preserved_for_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
                thread_staged_pages_1g_wf_preserved_for_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
            };
            assert(container_process_allocator_quota_wf(
                kernel.container_map, kernel.process_map, kernel.thread_map,
                kernel.allocator_4k_map, kernel.allocator_2m_map,
                kernel.allocator_1g_map,
            )) by {
                container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(
                    kernel.container_map, kernel.process_map,
                    old(kernel).thread_map, kernel.thread_map,
                    kernel.allocator_4k_map,
                );
                container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(
                    kernel.container_map, kernel.process_map,
                    old(kernel).thread_map, kernel.thread_map,
                    kernel.allocator_2m_map,
                );
                container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(
                    kernel.container_map, kernel.process_map,
                    old(kernel).thread_map, kernel.thread_map,
                    kernel.allocator_1g_map,
                );
            };
        };
        assert(kernel.process_management_inv()) by {
            assert({
                &&& container_endpoint_wf(
                    kernel.container_map, kernel.endpoint_map)
                &&& thread_endpoint_ref_counter_wf(
                    kernel.thread_map, kernel.endpoint_map)
                &&& thread_caller_callee_wf(kernel.thread_map)
            }) by {
                reveal(container_endpoint_wf);
                reveal(thread_endpoint_ref_counter_wf);
                reveal(thread_caller_callee_wf);
            };
            assert({
                &&& container_scheduler_wf(
                    kernel.container_map, kernel.scheduler_map)
                &&& container_thread_wf(
                    kernel.container_map, kernel.thread_map)
                &&& process_thread_wf(
                    kernel.process_map, kernel.thread_map)
                &&& thread_cpu_wf(
                    kernel.thread_map, kernel.cpu_array)
            }) by {
                reveal(container_scheduler_wf);
                reveal(container_thread_wf);
                reveal(process_thread_wf);
                reveal(thread_cpu_wf);
            };
            assert(thread_endpoint_queue_wf(
                kernel.thread_map, kernel.endpoint_map,
            )) by {
                seq_skip_lemma::<RwLockThreadPtr>();
                seq_remove_lemma_2::<RwLockThreadPtr>();
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
                reveal(endpoints_inv);
                reveal(LinkedList::wf_value_list);
                reveal(LinkedList::wf_map);
                reveal(thread_endpoint_ref_counter_wf);
                reveal(thread_endpoint_queue_wf);
            };
            assert(container_thread_endpoint_wf(
                kernel.container_map, kernel.thread_map, kernel.endpoint_map,
            )) by {
                reveal(container_endpoint_wf);
                reveal(thread_endpoint_ref_counter_wf);
                reveal(thread_endpoint_queue_wf);
                reveal(container_thread_endpoint_wf);
            };
            assert(container_thread_scheduler_wf(
                kernel.container_map, kernel.thread_map, kernel.scheduler_map,
            )) by {
                reveal(container_thread_wf);
                reveal(container_scheduler_wf);
                reveal(container_thread_scheduler_wf);
            };
        };
        assert({
            &&& cpu_dirty_map_wf(
                kernel.container_map, kernel.process_map, kernel.cpu_array,
                kernel.cpu_tlb, kernel.pagetable_map)
            &&& tlb_wf_spec(
                kernel.cpu_tlb, kernel.pagetable_map, kernel.cpu_array)
            &&& typed_lock_maps_aligned(kernel, &*lctx)
            &&& cpu_objects_unlocked_except(
                kernel.cpu_array, lctx.thread_id(), set![cpu_id])
            &&& page_objects_unlocked(kernel.page_array, lctx.thread_id())
            &&& container_objects_unlocked(
                kernel.container_map, lctx.thread_id())
            &&& process_objects_unlocked_except(
                kernel.process_map, lctx.thread_id(), set![process_ptr])
            &&& thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![current_thread_ptr, peer_thread_ptr])
            &&& endpoint_objects_unlocked_except(
                kernel.endpoint_map, lctx.thread_id(),
                set![channel_endpoint_ptr])
            &&& pagetable_objects_unlocked(
                kernel.pagetable_map, lctx.thread_id())
            &&& iommu_table_objects_unlocked(
                kernel.iommu_table_map, lctx.thread_id())
            &&& scheduler_objects_unlocked(
                kernel.scheduler_map, lctx.thread_id())
            &&& pcid_allocator_objects_unlocked(
                kernel.pcid_allocator_map, lctx.thread_id())
            &&& allocator_objects_unlocked(
                kernel.allocator_4k_map, lctx.thread_id())
            &&& allocator_objects_unlocked(
                kernel.allocator_2m_map, lctx.thread_id())
            &&& allocator_objects_unlocked(
                kernel.allocator_1g_map, lctx.thread_id())
        }) by {
            reveal(cpu_dirty_map_contains_container_processes);
            reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
            reveal(cpu_dirty_map_proc_pcid_match);
            reveal(cpu_dirty_map_contains_pagetable_pcid_match);
            reveal(container_cpu_wf);
            reveal(tlb_wf_spec);
            reveal(typed_lock_maps_aligned);
            reveal(cpu_objects_unlocked_except);
            reveal(process_objects_unlocked_except);
            reveal(thread_objects_unlocked_except);
            reveal(endpoint_objects_unlocked_except);
        };
    }

    kernel.wunlock_endpoint(
        channel_endpoint_ptr, Tracked(&mut *lctx),
        Tracked(channel_endpoint_lock_perm),
    );
    proof {
        assert({
            &&& endpoint_objects_unlocked(
                kernel.endpoint_map, lctx.thread_id())
            &&& kernel_k_to_kernel_u(*kernel)
                == kernel_k_to_kernel_u(*old(kernel))
        }) by {
            reveal(endpoint_objects_unlocked_except);
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                old(kernel), kernel,
            );
        };
        kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
        assert({
            &&& kernel.thread_map.spec_index(source_thread_ptr).view()
                .endpoint_descriptors.wf()
            &&& kernel.thread_map.spec_index(source_thread_ptr).view()
                .endpoint_descriptors.view().spec_index(
                    source_endpoint_index as int) == Some(payload_endpoint_ptr)
        }) by {
            reveal(thread_perms_wf);
        };
        assert(
            kernel.thread_map.perms_wf()
                && kernel.endpoint_map.perms_wf()
                && kernel.container_map.perms_wf()
        ) by {
            reveal(thread_perms_wf);
            reveal(endpoint_perms_wf);
            reveal(container_perms_wf);
        };
        assert({
            &&& kernel.process_map.dom().contains(process_ptr)
            &&& kernel.thread_map.dom().contains(current_thread_ptr)
            &&& kernel.thread_map.spec_index(current_thread_ptr).is_init()
            &&& kernel.thread_map.dom().contains(peer_thread_ptr)
            &&& kernel.thread_map.spec_index(peer_thread_ptr).is_init()
            &&& kernel.thread_map.spec_index(source_thread_ptr).view()
                .endpoint_descriptors.wf()
        }) by {
            reveal(thread_perms_wf);
        };
        assert(kernel.endpoint_map.dom().contains(
            payload_endpoint_ptr,
        )) by {
            reveal(thread_endpoint_ref_counter_wf);
        };
        assert({
            &&& kernel.endpoint_map.spec_index(payload_endpoint_ptr).is_init()
            &&& kernel.endpoint_map.lock_id_by_key(
                payload_endpoint_ptr).major == ENDPOINT_LOCK_MAJOR
        }) by {
            reveal(endpoint_perms_wf);
            reveal(endpoints_inv);
        };
    }
}

pub(super) fn ipc_finish_endpoint_transit(
    kernel: &mut KernelK,
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
        old(kernel).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
        current_thread_ptr != peer_thread_ptr,
        old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(kernel).cpu_array.spec_index(cpu_id).view().being_killed() == false,
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id()
            == old(kernel).cpu_array.spec_index(cpu_id).view()
                .locking_thread()->Write_lock_id,
        old(kernel).process_map.dom().contains(process_ptr),
        old(kernel).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
        old(kernel).process_map.spec_index(process_ptr).being_killed() == false,
        process_lock_perm.view().state() is WriteLock,
        process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        process_lock_perm.view().lock_id()
            == old(kernel).process_map.spec_index(process_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).thread_map.dom().contains(current_thread_ptr),
        old(kernel).thread_map.spec_index(current_thread_ptr)
            .wlocked_by(old(lctx)),
        old(kernel).thread_map.spec_index(current_thread_ptr)
            .being_killed() == false,
        old(kernel).thread_map.spec_index(current_thread_ptr).view().state
            == (ThreadState::RUNNING { cpu_id }),
        old(kernel).thread_map.spec_index(current_thread_ptr).view()
            .free_quota_pending_clean(),
        old(kernel).thread_map.spec_index(current_thread_ptr).view()
            .temp_alloc_clean(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id()
            == old(kernel).thread_map.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).endpoint_map.dom().contains(payload_endpoint_ptr),
        old(kernel).endpoint_map.spec_index(payload_endpoint_ptr)
            .wlocked_by(old(lctx)),
        payload_endpoint_lock_perm.view().state() is WriteLock,
        payload_endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        payload_endpoint_lock_perm.view().lock_id()
            == old(kernel).endpoint_map.spec_index(payload_endpoint_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).thread_map.dom().contains(peer_thread_ptr),
        old(kernel).thread_map.spec_index(peer_thread_ptr)
            .wlocked_by(old(lctx)),
        old(kernel).thread_map.spec_index(peer_thread_ptr)
            .being_killed() == false,
        old(kernel).thread_map.spec_index(peer_thread_ptr).view().state
            is IPC_ENDPOINT_TRANSIT,
        old(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .free_quota_pending_clean(),
        old(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .temp_alloc_clean(),
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id()
            == old(kernel).thread_map.spec_index(peer_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).scheduler_map.dom().contains(peer_scheduler_ptr),
        old(kernel).scheduler_map.spec_index(peer_scheduler_ptr)
            .wlocked_by(old(lctx)),
        peer_scheduler_lock_perm.view().state() is WriteLock,
        peer_scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_scheduler_lock_perm.view().lock_id()
            == old(kernel).scheduler_map.spec_index(peer_scheduler_ptr)
                .locking_thread()->Write_lock_id,
        {
            let peer_container = old(kernel).thread_map
                .spec_index(peer_thread_ptr).view().owning_container;
            &&& old(kernel).container_map.dom().contains(peer_container)
            &&& old(kernel).container_map.spec_index(peer_container)
                .view_rodata().view().scheduler == peer_scheduler_ptr
            &&& old(kernel).scheduler_map.spec_index(peer_scheduler_ptr)
                .view().owning_container == peer_container
        },
        !old(kernel).scheduler_map.spec_index(peer_scheduler_ptr).view()
            .queue.view().contains(peer_thread_ptr),
        cpu_objects_unlocked_except(
            old(kernel).cpu_array, old(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(old(kernel).page_array, old(lctx).thread_id()),
        container_objects_unlocked(
            old(kernel).container_map, old(lctx).thread_id()),
        process_objects_unlocked_except(
            old(kernel).process_map, old(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(
            old(kernel).thread_map, old(lctx).thread_id(),
            set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked_except(
            old(kernel).endpoint_map, old(lctx).thread_id(),
            set![payload_endpoint_ptr]),
        pagetable_objects_unlocked(
            old(kernel).pagetable_map, old(lctx).thread_id()),
        iommu_table_objects_unlocked(
            old(kernel).iommu_table_map, old(lctx).thread_id()),
        scheduler_objects_unlocked_except(
            old(kernel).scheduler_map, old(lctx).thread_id(),
            set![peer_scheduler_ptr]),
        pcid_allocator_objects_unlocked(
            old(kernel).pcid_allocator_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_4k_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_2m_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_1g_map, old(lctx).thread_id()),
        typed_lock_maps_aligned(old(kernel), old(lctx)),
    ensures
        ret == result,
        final(kernel).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
        final(lctx).no_locks_held(),
        final(kernel).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(kernel), final(lctx)),
{
    let ghost old_peer_thread_lock_id =
        kernel.thread_map.lock_id_by_key(peer_thread_ptr);
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked process_lock_perm = process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked payload_endpoint_lock_perm = payload_endpoint_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();
    let tracked peer_scheduler_lock_perm = peer_scheduler_lock_perm.get();

    assert(kernel.scheduler_map.spec_index(peer_scheduler_ptr).view()
        .queue.length != usize::MAX) by {
        scheduler_queue_len_bounded(&*kernel, peer_scheduler_ptr);
    };
    let (scheduler_node_addr, scheduler_node_perm) =
        ipc_schedule_endpoint_transit(
            &mut kernel.thread_map, Tracked(&*lctx),
            peer_thread_ptr, current_thread_ptr, result,
            Tracked(&peer_thread_lock_perm),
        );
    ipc_enqueue_scheduled_thread(
        &mut kernel.scheduler_map, Tracked(&*lctx),
        peer_scheduler_ptr, peer_thread_ptr,
        scheduler_node_addr, scheduler_node_perm,
        Tracked(&peer_scheduler_lock_perm),
    );

    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(
            KernelObjId::Thread(peer_thread_ptr),
            TypedHeldLock {
                lock_id: old_peer_thread_lock_id,
                mode: TypedLockMode::Write,
            },
            kernel.thread_map.lock_id_by_key(peer_thread_ptr),
        );
        assert(kernel.subsystems_inv()) by {
            assert({
                &&& thread_perms_wf(kernel.thread_map)
                &&& endpoint_perms_wf(kernel.endpoint_map)
                &&& scheduler_perms_wf(kernel.scheduler_map)
            }) by {
                reveal(thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
                reveal(thread_temp_alloc_empty_unless_wlocked);
                reveal(endpoint_perms_wf);
                reveal(endpoints_inv);
                reveal(scheduler_perms_wf);
            };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(kernel.memory_management_inv()) by {
            assert(thread_quota_4k_fields_unchanged(
                old(kernel).thread_map, kernel.thread_map,
            )) by {
                reveal(thread_quota_4k_fields_unchanged);
            };
            assert(thread_quota_2m_fields_unchanged(
                old(kernel).thread_map, kernel.thread_map,
            )) by {
                reveal(thread_quota_2m_fields_unchanged);
            };
            assert(thread_quota_1g_fields_unchanged(
                old(kernel).thread_map, kernel.thread_map,
            )) by {
                reveal(thread_quota_1g_fields_unchanged);
            };
            assert(thread_pages_wf(
                kernel.thread_map, kernel.page_array,
            )) by {
                reveal(thread_pages_wf);
            };
            assert(thread_staged_pages_wf(
                kernel.thread_map, kernel.page_array,
            )) by {
                thread_staged_pages_4k_wf_preserved_for_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
                thread_staged_pages_2m_wf_preserved_for_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
                thread_staged_pages_1g_wf_preserved_for_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
            };
            assert(endpoint_pages_wf(
                kernel.endpoint_map, kernel.page_array,
            )) by {
                reveal(endpoint_pages_wf);
            };
            assert(container_process_allocator_quota_wf(
                kernel.container_map, kernel.process_map, kernel.thread_map,
                kernel.allocator_4k_map, kernel.allocator_2m_map,
                kernel.allocator_1g_map,
            )) by {
                container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(
                    kernel.container_map, kernel.process_map,
                    old(kernel).thread_map, kernel.thread_map,
                    kernel.allocator_4k_map,
                );
                container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(
                    kernel.container_map, kernel.process_map,
                    old(kernel).thread_map, kernel.thread_map,
                    kernel.allocator_2m_map,
                );
                container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(
                    kernel.container_map, kernel.process_map,
                    old(kernel).thread_map, kernel.thread_map,
                    kernel.allocator_1g_map,
                );
            };
        };
        assert(kernel.process_management_inv()) by {
            assert(container_endpoint_wf(
                kernel.container_map, kernel.endpoint_map,
            )) by {
                reveal(container_endpoint_wf);
            };
            assert(thread_endpoint_ref_counter_wf(
                kernel.thread_map, kernel.endpoint_map,
            )) by {
                reveal(thread_endpoint_ref_counter_wf);
            };
            assert(thread_caller_callee_wf(kernel.thread_map)) by {
                reveal(thread_caller_callee_wf);
            };
            assert(thread_endpoint_queue_wf(
                kernel.thread_map, kernel.endpoint_map,
            )) by {
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
                reveal(endpoints_inv);
                reveal(thread_endpoint_ref_counter_wf);
                reveal(thread_endpoint_queue_wf);
            };
            assert(container_thread_endpoint_wf(
                kernel.container_map, kernel.thread_map, kernel.endpoint_map,
            )) by {
                reveal(container_thread_endpoint_wf);
            };
            assert(container_scheduler_wf(
                kernel.container_map, kernel.scheduler_map,
            )) by {
                reveal(container_scheduler_wf);
            };
            assert(container_thread_wf(
                kernel.container_map, kernel.thread_map,
            )) by {
                reveal(container_thread_wf);
            };
            assert(process_thread_wf(
                kernel.process_map, kernel.thread_map,
            )) by {
                reveal(process_thread_wf);
            };
            assert(thread_cpu_wf(
                kernel.thread_map, kernel.cpu_array,
            )) by {
                reveal(thread_cpu_wf);
            };
            assert(container_thread_scheduler_wf(
                kernel.container_map, kernel.thread_map, kernel.scheduler_map,
            )) by {
                seq_push_lemma::<RwLockThreadPtr>();
                reveal(container_thread_wf);
                reveal(container_scheduler_wf);
                reveal(container_thread_scheduler_wf);
                reveal(LinkedList::wf_value_list);
                reveal(LinkedList::wf_map);
            };
        };
        assert({
            &&& cpu_dirty_map_wf(
                kernel.container_map, kernel.process_map, kernel.cpu_array,
                kernel.cpu_tlb, kernel.pagetable_map)
            &&& tlb_wf_spec(
                kernel.cpu_tlb, kernel.pagetable_map, kernel.cpu_array)
            &&& typed_lock_maps_aligned(kernel, &*lctx)
            &&& cpu_objects_unlocked_except(
                kernel.cpu_array, lctx.thread_id(), set![cpu_id])
            &&& page_objects_unlocked(kernel.page_array, lctx.thread_id())
            &&& container_objects_unlocked(kernel.container_map, lctx.thread_id())
            &&& process_objects_unlocked_except(
                kernel.process_map, lctx.thread_id(), set![process_ptr])
            &&& thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![current_thread_ptr, peer_thread_ptr])
            &&& endpoint_objects_unlocked_except(
                kernel.endpoint_map, lctx.thread_id(), set![payload_endpoint_ptr])
            &&& pagetable_objects_unlocked(kernel.pagetable_map, lctx.thread_id())
            &&& iommu_table_objects_unlocked(kernel.iommu_table_map, lctx.thread_id())
            &&& scheduler_objects_unlocked_except(
                kernel.scheduler_map, lctx.thread_id(), set![peer_scheduler_ptr])
            &&& pcid_allocator_objects_unlocked(
                kernel.pcid_allocator_map, lctx.thread_id())
            &&& allocator_objects_unlocked(kernel.allocator_4k_map, lctx.thread_id())
            &&& allocator_objects_unlocked(kernel.allocator_2m_map, lctx.thread_id())
            &&& allocator_objects_unlocked(kernel.allocator_1g_map, lctx.thread_id())
        }) by {
            reveal(cpu_dirty_map_contains_container_processes);
            reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
            reveal(cpu_dirty_map_proc_pcid_match);
            reveal(cpu_dirty_map_contains_pagetable_pcid_match);
            reveal(container_cpu_wf);
            reveal(tlb_wf_spec);
            reveal(typed_lock_maps_aligned);
            reveal(cpu_objects_unlocked_except);
            reveal(process_objects_unlocked_except);
            reveal(thread_objects_unlocked_except);
            reveal(endpoint_objects_unlocked_except);
            reveal(scheduler_objects_unlocked_except);
        };
    }

    kernel.wunlock_thread(
        peer_thread_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm),
    );
    kernel.wunlock_thread(
        current_thread_ptr, Tracked(&mut *lctx),
        Tracked(current_thread_lock_perm),
    );
    kernel.wunlock_scheduler(
        peer_scheduler_ptr, Tracked(&mut *lctx),
        Tracked(peer_scheduler_lock_perm),
    );
    kernel.wunlock_endpoint(
        payload_endpoint_ptr, Tracked(&mut *lctx),
        Tracked(payload_endpoint_lock_perm),
    );
    kernel.wunlock_process(
        process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm),
    );
    kernel.wunlock_cpu(
        cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm),
    );
    proof {
        assert({
            &&& kernel.all_objects_unlocked(&*lctx)
            &&& kernel_k_to_kernel_u(*kernel)
                == kernel_k_to_kernel_u(*old(kernel))
        }) by {
            reveal(cpu_objects_unlocked_except);
            reveal(process_objects_unlocked_except);
            reveal(thread_objects_unlocked_except);
            reveal(endpoint_objects_unlocked_except);
            reveal(scheduler_objects_unlocked_except);
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                old(kernel), kernel,
            );
        };
        steps.end_kernel_step(&*kernel, &*lctx);
    }
    result
}

pub(super) fn ipc_rendezvous_endpoint(
    kernel: &mut KernelK,
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
        old(kernel).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
        current_thread_ptr != peer_thread_ptr,
        source_thread_ptr == current_thread_ptr
            && receiver_thread_ptr == peer_thread_ptr
            || source_thread_ptr == peer_thread_ptr
                && receiver_thread_ptr == current_thread_ptr,
        edp_idx_valid(source_endpoint_index),
        edp_idx_valid(target_endpoint_index),
        old(kernel).thread_map.dom().contains(source_thread_ptr),
        old(kernel).thread_map.spec_index(source_thread_ptr).view()
            .endpoint_descriptors.wf(),
        old(kernel).thread_map.dom().contains(receiver_thread_ptr),
        old(kernel).thread_map.spec_index(receiver_thread_ptr).view()
            .endpoint_descriptors.wf(),
        old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(kernel).cpu_array.spec_index(cpu_id).view().being_killed() == false,
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id()
            == old(kernel).cpu_array.spec_index(cpu_id).view()
                .locking_thread()->Write_lock_id,
        old(kernel).process_map.dom().contains(process_ptr),
        old(kernel).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
        old(kernel).process_map.spec_index(process_ptr).being_killed() == false,
        process_lock_perm.view().state() is WriteLock,
        process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        process_lock_perm.view().lock_id()
            == old(kernel).process_map.spec_index(process_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).thread_map.dom().contains(current_thread_ptr),
        old(kernel).thread_map.spec_index(current_thread_ptr)
            .wlocked_by(old(lctx)),
        old(kernel).thread_map.spec_index(current_thread_ptr)
            .being_killed() == false,
        old(kernel).thread_map.spec_index(current_thread_ptr).view().state
            == (ThreadState::RUNNING { cpu_id }),
        old(kernel).cpu_array.spec_index(cpu_id).view().view().state
            is Running,
        old(kernel).cpu_array.spec_index(cpu_id).view().view().current_process
            == Some(process_ptr),
        old(kernel).cpu_array.spec_index(cpu_id).view().view().current_thread
            == Some(current_thread_ptr),
        old(kernel).thread_map.spec_index(current_thread_ptr).view()
            .owning_proc == process_ptr,
        old(kernel).thread_map.spec_index(current_thread_ptr).view()
            .free_quota_pending_clean(),
        old(kernel).thread_map.spec_index(current_thread_ptr).view()
            .temp_alloc_clean(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id()
            == old(kernel).thread_map.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).endpoint_map.dom().contains(channel_endpoint_ptr),
        old(kernel).endpoint_map.spec_index(channel_endpoint_ptr)
            .wlocked_by(old(lctx)),
        channel_endpoint_lock_perm.view().state() is WriteLock,
        channel_endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        channel_endpoint_lock_perm.view().lock_id()
            == old(kernel).endpoint_map.spec_index(channel_endpoint_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).thread_map.dom().contains(peer_thread_ptr),
        old(kernel).thread_map.spec_index(peer_thread_ptr)
            .wlocked_by(old(lctx)),
        old(kernel).thread_map.spec_index(peer_thread_ptr)
            .being_killed() == false,
        old(kernel).thread_map.spec_index(peer_thread_ptr).view().state
            is SENDING
            || old(kernel).thread_map.spec_index(peer_thread_ptr).view().state
                is RECEIVING,
        old(kernel).thread_map.spec_index(peer_thread_ptr).view().ipc_payload
            is Endpoint,
        old(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .free_quota_pending_clean(),
        old(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .temp_alloc_clean(),
        old(kernel).thread_map.spec_index(peer_thread_ptr).view()
            .blocking_endpoint_ptr == Some(channel_endpoint_ptr),
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id()
            == old(kernel).thread_map.spec_index(peer_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(kernel).endpoint_map.spec_index(channel_endpoint_ptr).view()
            .queue.len() != 0,
        old(kernel).endpoint_map.spec_index(channel_endpoint_ptr).view()
            .queue.view().spec_index(0) == peer_thread_ptr,
        cpu_objects_unlocked_except(
            old(kernel).cpu_array, old(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(old(kernel).page_array, old(lctx).thread_id()),
        container_objects_unlocked(
            old(kernel).container_map, old(lctx).thread_id()),
        process_objects_unlocked_except(
            old(kernel).process_map, old(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(
            old(kernel).thread_map, old(lctx).thread_id(),
            set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked_except(
            old(kernel).endpoint_map, old(lctx).thread_id(),
            set![channel_endpoint_ptr]),
        pagetable_objects_unlocked(
            old(kernel).pagetable_map, old(lctx).thread_id()),
        iommu_table_objects_unlocked(
            old(kernel).iommu_table_map, old(lctx).thread_id()),
        scheduler_objects_unlocked(
            old(kernel).scheduler_map, old(lctx).thread_id()),
        pcid_allocator_objects_unlocked(
            old(kernel).pcid_allocator_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_4k_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_2m_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_1g_map, old(lctx).thread_id()),
        typed_lock_maps_aligned(old(kernel), old(lctx)),
    ensures
        ret is Success
            || ret is ErrorIpcEndpointSourceInvalid
            || ret is ErrorIpcEndpointTargetInUse
            || ret is ErrorIpcEndpointOwnerMismatch,
        final(kernel).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
        final(lctx).no_locks_held(),
        final(kernel).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(kernel), final(lctx)),
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked process_lock_perm = process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked channel_endpoint_lock_perm =
        channel_endpoint_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();

    proof {
        assert({
            &&& kernel.thread_map.perms_wf()
            &&& kernel.thread_map.spec_index(current_thread_ptr).is_init()
            &&& kernel.thread_map.spec_index(peer_thread_ptr).is_init()
        }) by {
            reveal(thread_perms_wf);
        };
    }
    let source_endpoint_option = if source_thread_ptr == current_thread_ptr {
        *kernel.thread_map.borrow(
            current_thread_ptr, Tracked(&current_thread_lock_perm),
        ).endpoint_descriptors.get(source_endpoint_index)
    } else {
        *kernel.thread_map.borrow(
            peer_thread_ptr, Tracked(&peer_thread_lock_perm),
        ).endpoint_descriptors.get(source_endpoint_index)
    };
    let target_endpoint_option = if receiver_thread_ptr == current_thread_ptr {
        *kernel.thread_map.borrow(
            current_thread_ptr, Tracked(&current_thread_lock_perm),
        ).endpoint_descriptors.get(target_endpoint_index)
    } else {
        *kernel.thread_map.borrow(
            peer_thread_ptr, Tracked(&peer_thread_lock_perm),
        ).endpoint_descriptors.get(target_endpoint_index)
    };
    if let None = source_endpoint_option {
        return ipc_schedule_waiting_peer_and_finish(
            kernel, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            process_ptr, current_thread_ptr, channel_endpoint_ptr,
            peer_thread_ptr, RetValueType::ErrorIpcEndpointSourceInvalid,
            Tracked(cpu_lock_perm), Tracked(process_lock_perm),
            Tracked(current_thread_lock_perm),
            Tracked(channel_endpoint_lock_perm),
            Tracked(peer_thread_lock_perm),
        );
    }
    if let Some(_) = target_endpoint_option {
        return ipc_schedule_waiting_peer_and_finish(
            kernel, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            process_ptr, current_thread_ptr, channel_endpoint_ptr,
            peer_thread_ptr, RetValueType::ErrorIpcEndpointTargetInUse,
            Tracked(cpu_lock_perm), Tracked(process_lock_perm),
            Tracked(current_thread_lock_perm),
            Tracked(channel_endpoint_lock_perm),
            Tracked(peer_thread_lock_perm),
        );
    }
    let payload_endpoint_ptr = source_endpoint_option.unwrap();

    ipc_begin_endpoint_transfer(
        kernel, Tracked(&mut *lctx), Tracked(&mut *steps),
        cpu_id, process_ptr, current_thread_ptr, channel_endpoint_ptr,
        peer_thread_ptr, source_thread_ptr,
        source_endpoint_index, payload_endpoint_ptr,
        Tracked(&cpu_lock_perm), Tracked(&process_lock_perm),
        Tracked(&current_thread_lock_perm),
        Tracked(channel_endpoint_lock_perm),
        Tracked(&peer_thread_lock_perm),
    );

    proof {
        assert(
            !kernel.endpoint_map.spec_index(payload_endpoint_ptr)
                .locked_by_thread(lctx.thread_id())
        ) by {
            reveal(endpoint_objects_unlocked);
        };
        assert(lctx.lock_id_acyclic(
            kernel.endpoint_map.lock_id_by_key(payload_endpoint_ptr),
        )) by {
            reveal(process_perms_wf);
            reveal(thread_perms_wf);
            reveal(endpoint_perms_wf);
        };
    }
    let Tracked(payload_endpoint_lock_perm) = kernel.wlock_endpoint(
        payload_endpoint_ptr, Tracked(&mut *lctx),
    );
    proof {
        assert({
            &&& kernel.endpoint_map.perms_wf()
            &&& kernel.endpoint_map.spec_index(payload_endpoint_ptr).is_init()
            &&& kernel.thread_map.perms_wf()
            &&& kernel.thread_map.spec_index(current_thread_ptr).is_init()
            &&& kernel.thread_map.spec_index(peer_thread_ptr).is_init()
        }) by {
            reveal(endpoint_perms_wf);
            reveal(thread_perms_wf);
        };
    }
    let payload_endpoint_ref = kernel.endpoint_map.borrow(
        payload_endpoint_ptr, Tracked(&payload_endpoint_lock_perm),
    );
    let endpoint_owner = payload_endpoint_ref.owning_container;
    let receiver_container = if receiver_thread_ptr == current_thread_ptr {
        kernel.thread_map.borrow(
            current_thread_ptr, Tracked(&current_thread_lock_perm),
        ).owning_container
    } else {
        kernel.thread_map.borrow(
            peer_thread_ptr, Tracked(&peer_thread_lock_perm),
        ).owning_container
    };
    proof {
        assert({
            &&& kernel.container_map.dom().contains(endpoint_owner)
            &&& kernel.container_map.dom().contains(receiver_container)
            &&& container_perms_wf(kernel.container_map)
            &&& container_tree_wf(
                kernel.root_container, kernel.container_map)
        }) by {
            reveal(container_endpoint_wf);
            reveal(container_thread_wf);
        };
    }
    let owner_compatible = if endpoint_owner == receiver_container {
        true
    } else {
        container_tree_check_is_ancestor(
            kernel.root_container, &kernel.container_map,
            endpoint_owner, receiver_container,
        )
    };
    let result = if owner_compatible {
        if receiver_thread_ptr == current_thread_ptr {
            ipc_copy_endpoint_reference(
                kernel, receiver_thread_ptr, target_endpoint_index,
                payload_endpoint_ptr, Tracked(&*lctx),
                Tracked(&current_thread_lock_perm),
                Tracked(&payload_endpoint_lock_perm),
            );
        } else {
            ipc_copy_endpoint_reference(
                kernel, receiver_thread_ptr, target_endpoint_index,
                payload_endpoint_ptr, Tracked(&*lctx),
                Tracked(&peer_thread_lock_perm),
                Tracked(&payload_endpoint_lock_perm),
            );
        }
        RetValueType::Success
    } else {
        RetValueType::ErrorIpcEndpointOwnerMismatch
    };

    proof {
        assert(
            kernel.thread_map.perms_wf()
                && kernel.thread_map.spec_index(peer_thread_ptr).is_init()
        ) by {
            reveal(thread_perms_wf);
        };
    }
    let peer_container_ptr = kernel.thread_map.borrow(
        peer_thread_ptr, Tracked(&peer_thread_lock_perm),
    ).owning_container;
    proof {
        assert(
            kernel.container_map.perms_wf()
                && kernel.container_map.dom().contains(peer_container_ptr)
        ) by {
            reveal(container_perms_wf);
            reveal(container_thread_wf);
        };
    }
    let peer_scheduler_ptr = kernel.container_map
        .borrow_rodata(peer_container_ptr).borrow().scheduler;
    proof {
        assert({
            &&& kernel.scheduler_map.dom().contains(peer_scheduler_ptr)
            &&& !kernel.scheduler_map.spec_index(peer_scheduler_ptr)
                .locked_by_thread(lctx.thread_id())
            &&& lctx.lock_id_acyclic(
                kernel.scheduler_map.lock_id_by_key(peer_scheduler_ptr))
        }) by {
            reveal(container_thread_wf);
            reveal(container_scheduler_wf);
            reveal(scheduler_perms_wf);
            reveal(scheduler_objects_unlocked);
            reveal(process_perms_wf);
            reveal(thread_perms_wf);
            reveal(endpoint_perms_wf);
        };
    }
    let Tracked(peer_scheduler_lock_perm) = kernel.wlock_scheduler(
        peer_scheduler_ptr, Tracked(&mut *lctx),
    );
    proof {
        assert({
            &&& kernel.container_map.spec_index(peer_container_ptr)
                .view_rodata().view().scheduler == peer_scheduler_ptr
            &&& kernel.scheduler_map.spec_index(peer_scheduler_ptr).view()
                .owning_container == peer_container_ptr
            &&& !kernel.scheduler_map.spec_index(peer_scheduler_ptr).view()
                .queue.view().contains(peer_thread_ptr)
            &&& cpu_objects_unlocked_except(
                kernel.cpu_array, lctx.thread_id(), set![cpu_id])
            &&& page_objects_unlocked(
                kernel.page_array, lctx.thread_id())
            &&& container_objects_unlocked(
                kernel.container_map, lctx.thread_id())
            &&& process_objects_unlocked_except(
                kernel.process_map, lctx.thread_id(), set![process_ptr])
            &&& thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![current_thread_ptr, peer_thread_ptr])
            &&& endpoint_objects_unlocked_except(
                kernel.endpoint_map, lctx.thread_id(),
                set![payload_endpoint_ptr])
            &&& pagetable_objects_unlocked(
                kernel.pagetable_map, lctx.thread_id())
            &&& iommu_table_objects_unlocked(
                kernel.iommu_table_map, lctx.thread_id())
            &&& scheduler_objects_unlocked_except(
                kernel.scheduler_map, lctx.thread_id(),
                set![peer_scheduler_ptr])
            &&& pcid_allocator_objects_unlocked(
                kernel.pcid_allocator_map, lctx.thread_id())
            &&& allocator_objects_unlocked(
                kernel.allocator_4k_map, lctx.thread_id())
            &&& allocator_objects_unlocked(
                kernel.allocator_2m_map, lctx.thread_id())
            &&& allocator_objects_unlocked(
                kernel.allocator_1g_map, lctx.thread_id())
        }) by {
            reveal(container_scheduler_wf);
            reveal(container_thread_scheduler_wf);
            reveal(cpu_objects_unlocked_except);
            reveal(process_objects_unlocked_except);
            reveal(thread_objects_unlocked_except);
            reveal(endpoint_objects_unlocked_except);
            reveal(scheduler_objects_unlocked_except);
        };
    }
    ipc_finish_endpoint_transit(
        kernel, Tracked(&mut *lctx), Tracked(&mut *steps),
        cpu_id, process_ptr, current_thread_ptr, payload_endpoint_ptr,
        peer_thread_ptr, peer_scheduler_ptr, result,
        Tracked(cpu_lock_perm), Tracked(process_lock_perm),
        Tracked(current_thread_lock_perm),
        Tracked(payload_endpoint_lock_perm),
        Tracked(peer_thread_lock_perm),
        Tracked(peer_scheduler_lock_perm),
    )
}

}
