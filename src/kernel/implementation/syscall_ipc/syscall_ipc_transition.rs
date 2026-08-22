use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_queue::{
    ipc_block_thread_on_endpoint,
    ipc_dequeue_endpoint_waiter,
    ipc_enqueue_endpoint_waiter,
    ipc_enqueue_scheduled_thread,
    ipc_schedule_endpoint_waiter,
};
verus! {

    pub(super) fn ipc_release_current_endpoint_and_finish(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        current_thread_ptr: RwLockThreadPtr,
        endpoint_ptr: RwLockEndpointPtr,
        error: RetValueType,
        cpu_lock_perm: Tracked<LockPerm>,
        process_lock_perm: Tracked<LockPerm>,
        current_thread_lock_perm: Tracked<LockPerm>,
        endpoint_lock_perm: Tracked<LockPerm>,
    ) -> (ret: RetValueType)
        requires
            old(kernel).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
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
            old(kernel).thread_map.spec_index(current_thread_ptr).view()
                .free_quota_pending_clean(),
            old(kernel).thread_map.spec_index(current_thread_ptr).view()
                .temp_alloc_clean(),
            current_thread_lock_perm.view().state() is WriteLock,
            current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.view().lock_id()
                == old(kernel).thread_map.spec_index(current_thread_ptr)
                    .locking_thread()->Write_lock_id,
            old(kernel).endpoint_map.dom().contains(endpoint_ptr),
            old(kernel).endpoint_map.spec_index(endpoint_ptr)
                .wlocked_by(old(lctx)),
            endpoint_lock_perm.view().state() is WriteLock,
            endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.view().lock_id()
                == old(kernel).endpoint_map.spec_index(endpoint_ptr)
                    .locking_thread()->Write_lock_id,
            old(lctx).lock_id_set() =~= set![
                (
                    old(kernel).cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id),
                ),
                (
                    old(kernel).process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr),
                ),
                (
                    old(kernel).thread_map.lock_id_by_key(current_thread_ptr),
                    KernelObjId::Thread(current_thread_ptr),
                ),
                (
                    old(kernel).endpoint_map.lock_id_by_key(endpoint_ptr),
                    KernelObjId::Endpoint(endpoint_ptr),
                ),
            ],
            cpu_objects_unlocked_except(
                old(kernel).cpu_array, old(lctx).thread_id(), set![cpu_id]),
            page_objects_unlocked(old(kernel).page_array, old(lctx).thread_id()),
            container_objects_unlocked(old(kernel).container_map, old(lctx).thread_id()),
            process_objects_unlocked_except(
                old(kernel).process_map, old(lctx).thread_id(), set![process_ptr]),
            thread_objects_unlocked_except(
                old(kernel).thread_map, old(lctx).thread_id(), set![current_thread_ptr]),
            endpoint_objects_unlocked_except(
                old(kernel).endpoint_map, old(lctx).thread_id(), set![endpoint_ptr]),
            pagetable_objects_unlocked(old(kernel).pagetable_map, old(lctx).thread_id()),
            iommu_table_objects_unlocked(old(kernel).iommu_table_map, old(lctx).thread_id()),
            scheduler_objects_unlocked(old(kernel).scheduler_map, old(lctx).thread_id()),
            pcid_allocator_objects_unlocked(
                old(kernel).pcid_allocator_map, old(lctx).thread_id()),
            allocator_objects_unlocked(old(kernel).allocator_4k_map, old(lctx).thread_id()),
            allocator_objects_unlocked(old(kernel).allocator_2m_map, old(lctx).thread_id()),
            allocator_objects_unlocked(old(kernel).allocator_1g_map, old(lctx).thread_id()),
            lock_id_aligned(old(kernel), old(lctx)),
        ensures
            ret == error,
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(kernel).all_objects_unlocked(final(lctx)),
            lock_id_aligned(final(kernel), final(lctx)),
    {
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked current_thread_lock_perm = current_thread_lock_perm.get();
        let tracked endpoint_lock_perm = endpoint_lock_perm.get();

        kernel.wunlock_endpoint(
            endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm),
        );
        kernel.wunlock_thread(
            current_thread_ptr, Tracked(&mut *lctx),
            Tracked(current_thread_lock_perm),
        );
        kernel.wunlock_process(
            process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm),
        );
        kernel.wunlock_cpu(
            cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm),
        );
        proof {
            assert(
                kernel.all_objects_unlocked(&*lctx)
                && kernel_k_to_kernel_u(*kernel)
                    == kernel_k_to_kernel_u(*old(kernel))
            ) by {
                reveal(cpu_objects_unlocked_except);
                reveal(process_objects_unlocked_except);
                reveal(thread_objects_unlocked_except);
                reveal(endpoint_objects_unlocked_except);
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                    old(kernel), kernel,
                );
            };
            steps.end_kernel_step(&*kernel, &*lctx);
        }
        error
    }
    pub(super) fn ipc_match_ordinary(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        current_thread_ptr: RwLockThreadPtr,
        endpoint_ptr: RwLockEndpointPtr,
        peer_thread_ptr: RwLockThreadPtr,
        peer_scheduler_ptr: RwLockSchedulerPtr,
        cpu_lock_perm: Tracked<LockPerm>,
        process_lock_perm: Tracked<LockPerm>,
        current_thread_lock_perm: Tracked<LockPerm>,
        endpoint_lock_perm: Tracked<LockPerm>,
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
            old(kernel).thread_map.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
            old(kernel).thread_map.spec_index(current_thread_ptr).being_killed() == false,
            current_thread_lock_perm.view().state() is WriteLock,
            current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.view().lock_id()
                == old(kernel).thread_map.spec_index(current_thread_ptr)
                    .locking_thread()->Write_lock_id,
            old(kernel).endpoint_map.dom().contains(endpoint_ptr),
            old(kernel).endpoint_map.spec_index(endpoint_ptr).wlocked_by(old(lctx)),
            endpoint_lock_perm.view().state() is WriteLock,
            endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.view().lock_id()
                == old(kernel).endpoint_map.spec_index(endpoint_ptr)
                    .locking_thread()->Write_lock_id,
            old(kernel).thread_map.dom().contains(peer_thread_ptr),
            old(kernel).thread_map.spec_index(peer_thread_ptr).wlocked_by(old(lctx)),
            old(kernel).thread_map.spec_index(peer_thread_ptr).being_killed() == false,
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
            old(kernel).cpu_array.spec_index(cpu_id).view().view().state is Running,
            old(kernel).cpu_array.spec_index(cpu_id).view().view().current_process
                == Some(process_ptr),
            old(kernel).cpu_array.spec_index(cpu_id).view().view().current_thread
                == Some(current_thread_ptr),
            old(kernel).thread_map.spec_index(current_thread_ptr).view().state
                == (ThreadState::RUNNING { cpu_id }),
            old(kernel).thread_map.spec_index(current_thread_ptr).view().owning_proc
                == process_ptr,
            old(kernel).thread_map.spec_index(current_thread_ptr).view()
                .free_quota_pending_clean(),
            old(kernel).thread_map.spec_index(current_thread_ptr).view()
                .temp_alloc_clean(),
            old(kernel).thread_map.spec_index(peer_thread_ptr).view().state
                is SENDING
                || old(kernel).thread_map.spec_index(peer_thread_ptr).view().state
                    is RECEIVING,
            old(kernel).thread_map.spec_index(peer_thread_ptr).view()
                .blocking_endpoint_ptr == Some(endpoint_ptr),
            old(kernel).thread_map.spec_index(peer_thread_ptr).view()
                .free_quota_pending_clean(),
            old(kernel).thread_map.spec_index(peer_thread_ptr).view()
                .temp_alloc_clean(),
            old(kernel).endpoint_map.spec_index(endpoint_ptr).view().queue.len()
                != 0,
            old(kernel).endpoint_map.spec_index(endpoint_ptr).view().queue.view()
                .spec_index(0) == peer_thread_ptr,
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
            old(lctx).lock_id_set() =~= set![
                (
                    old(kernel).cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id),
                ),
                (
                    old(kernel).process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr),
                ),
                (
                    old(kernel).thread_map.lock_id_by_key(current_thread_ptr),
                    KernelObjId::Thread(current_thread_ptr),
                ),
                (
                    old(kernel).endpoint_map.lock_id_by_key(endpoint_ptr),
                    KernelObjId::Endpoint(endpoint_ptr),
                ),
                (
                    old(kernel).thread_map.lock_id_by_key(peer_thread_ptr),
                    KernelObjId::Thread(peer_thread_ptr),
                ),
                (
                    old(kernel).scheduler_map.lock_id_by_key(peer_scheduler_ptr),
                    KernelObjId::Scheduler(peer_scheduler_ptr),
                ),
            ],
            cpu_objects_unlocked_except(
                old(kernel).cpu_array, old(lctx).thread_id(), set![cpu_id]),
            page_objects_unlocked(old(kernel).page_array, old(lctx).thread_id()),
            container_objects_unlocked(old(kernel).container_map, old(lctx).thread_id()),
            process_objects_unlocked_except(
                old(kernel).process_map, old(lctx).thread_id(), set![process_ptr]),
            thread_objects_unlocked_except(
                old(kernel).thread_map, old(lctx).thread_id(),
                set![current_thread_ptr, peer_thread_ptr]),
            endpoint_objects_unlocked_except(
                old(kernel).endpoint_map, old(lctx).thread_id(), set![endpoint_ptr]),
            pagetable_objects_unlocked(old(kernel).pagetable_map, old(lctx).thread_id()),
            iommu_table_objects_unlocked(old(kernel).iommu_table_map, old(lctx).thread_id()),
            scheduler_objects_unlocked_except(
                old(kernel).scheduler_map, old(lctx).thread_id(), set![peer_scheduler_ptr]),
            pcid_allocator_objects_unlocked(
                old(kernel).pcid_allocator_map, old(lctx).thread_id()),
            allocator_objects_unlocked(old(kernel).allocator_4k_map, old(lctx).thread_id()),
            allocator_objects_unlocked(old(kernel).allocator_2m_map, old(lctx).thread_id()),
            allocator_objects_unlocked(old(kernel).allocator_1g_map, old(lctx).thread_id()),
            lock_id_aligned(old(kernel), old(lctx)),
        ensures
            ret is Success,
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(kernel).all_objects_unlocked(final(lctx)),
            lock_id_aligned(final(kernel), final(lctx)),
    {
        let ghost old_peer_thread_lock_id =
            kernel.thread_map.lock_id_by_key(peer_thread_ptr);
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked current_thread_lock_perm = current_thread_lock_perm.get();
        let tracked endpoint_lock_perm = endpoint_lock_perm.get();
        let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();
        let tracked peer_scheduler_lock_perm =
            peer_scheduler_lock_perm.get();

        let (_, Tracked(endpoint_node_perm)) =
            ipc_dequeue_endpoint_waiter(
                &mut kernel.endpoint_map, Tracked(&*lctx),
                endpoint_ptr, peer_thread_ptr,
                Tracked(&endpoint_lock_perm),
            );
        proof {
            assert({
                let peer_node_addr = old(kernel).thread_map
                    .spec_index(peer_thread_ptr).view()
                    .endpoint_linkedlist_node.addr();
                &&& old(kernel).endpoint_map.spec_index(endpoint_ptr)
                    .view().queue.map().dom().contains(peer_node_addr)
                &&& old(kernel).endpoint_map.spec_index(endpoint_ptr)
                    .view().queue.map().spec_index(peer_node_addr)
                        == peer_thread_ptr
                &&& endpoint_node_perm.addr()
                    == old(kernel).thread_map.spec_index(peer_thread_ptr)
                        .view().endpoint_linkedlist_node.addr()
            }) by {
                reveal(thread_endpoint_queue_wf);
                reveal(endpoint_perms_wf);
                reveal(endpoints_inv);
                reveal(LinkedList::wf_map);
            };
        }
        let (scheduler_node_addr, scheduler_node_perm) =
            ipc_schedule_endpoint_waiter(
                &mut kernel.thread_map, Tracked(&*lctx),
                peer_thread_ptr, current_thread_ptr,
                Tracked(endpoint_node_perm),
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
                old_peer_thread_lock_id,
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
                assert(
                    thread_pages_wf(kernel.thread_map, kernel.page_array)
                    && endpoint_pages_wf(kernel.endpoint_map, kernel.page_array)
                ) by {
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
                assert(container_process_allocator_quota_4k_wf(
                    kernel.container_map, kernel.process_map,
                    kernel.thread_map, kernel.allocator_4k_map,
                )) by {
                    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(
                        kernel.container_map, kernel.process_map,
                        old(kernel).thread_map, kernel.thread_map,
                        kernel.allocator_4k_map,
                    );
                };
                assert(container_process_allocator_quota_2m_wf(
                    kernel.container_map, kernel.process_map,
                    kernel.thread_map, kernel.allocator_2m_map,
                )) by {
                    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(
                        kernel.container_map, kernel.process_map,
                        old(kernel).thread_map, kernel.thread_map,
                        kernel.allocator_2m_map,
                    );
                };
                assert(container_process_allocator_quota_1g_wf(
                    kernel.container_map, kernel.process_map,
                    kernel.thread_map, kernel.allocator_1g_map,
                )) by {
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
                }) by {
                    reveal(container_scheduler_wf);
                    reveal(container_thread_wf);
                    reveal(process_thread_wf);
                };
                assert({
                    &&& container_cpu_wf(
                        kernel.container_map, kernel.cpu_array)
                    &&& process_cpu_wf(
                        kernel.process_map, kernel.cpu_array)
                    &&& thread_cpu_wf(
                        kernel.thread_map, kernel.cpu_array)
                }) by {
                    reveal(container_cpu_wf);
                    reveal(process_cpu_wf);
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
                    assert({
                        let peer_container = kernel.thread_map
                            .spec_index(peer_thread_ptr).view()
                            .owning_container;
                        let scheduler_ptr = kernel.container_map
                            .spec_index(peer_container).view_rodata()
                            .view().scheduler;
                        let scheduler_node_addr = kernel.thread_map
                            .spec_index(peer_thread_ptr).view()
                            .scheduler_linkedlist_node.addr();
                        &&& scheduler_ptr == peer_scheduler_ptr
                        &&& kernel.scheduler_map.spec_index(scheduler_ptr)
                            .view().queue.view().contains(peer_thread_ptr)
                        &&& kernel.scheduler_map.spec_index(scheduler_ptr)
                            .view().queue.map().dom()
                            .contains(scheduler_node_addr)
                        &&& kernel.scheduler_map.spec_index(scheduler_ptr)
                            .view().queue.map()
                            .spec_index(scheduler_node_addr)
                                == peer_thread_ptr
                    }) by {
                        seq_push_lemma::<RwLockThreadPtr>();
                    };
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
                &&& lock_id_aligned(kernel, &*lctx)
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
                    kernel.endpoint_map, lctx.thread_id(), set![endpoint_ptr])
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
                reveal(lock_id_aligned);
                reveal(cpu_objects_unlocked_except);
                reveal(process_objects_unlocked_except);
                reveal(thread_objects_unlocked_except);
                reveal(endpoint_objects_unlocked_except);
                reveal(scheduler_objects_unlocked_except);
            };
        }

        kernel.wunlock_thread(
            peer_thread_ptr, Tracked(&mut *lctx),
            Tracked(peer_thread_lock_perm),
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
            endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm),
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
        RetValueType::Success
    }

    pub(super) fn ipc_block_current(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        current_thread_ptr: RwLockThreadPtr,
        endpoint_ptr: RwLockEndpointPtr,
        endpoint_index: EndpointIdx,
        waiting_state: ThreadState,
        pt_regs: &Registers,
        cpu_lock_perm: Tracked<LockPerm>,
        process_lock_perm: Tracked<LockPerm>,
        current_thread_lock_perm: Tracked<LockPerm>,
        endpoint_lock_perm: Tracked<LockPerm>,
    ) -> (ret: RetValueType)
        requires
            old(kernel).inv(),
            index_valid(NUM_CPUS, cpu_id),
            edp_idx_valid(endpoint_index),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
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
            old(kernel).thread_map.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
            old(kernel).thread_map.spec_index(current_thread_ptr).being_killed() == false,
            current_thread_lock_perm.view().state() is WriteLock,
            current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.view().lock_id()
                == old(kernel).thread_map.spec_index(current_thread_ptr)
                    .locking_thread()->Write_lock_id,
            old(kernel).endpoint_map.dom().contains(endpoint_ptr),
            old(kernel).endpoint_map.spec_index(endpoint_ptr).wlocked_by(old(lctx)),
            endpoint_lock_perm.view().state() is WriteLock,
            endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.view().lock_id()
                == old(kernel).endpoint_map.spec_index(endpoint_ptr)
                    .locking_thread()->Write_lock_id,
            old(kernel).cpu_array.spec_index(cpu_id).view().view().state is Running,
            old(kernel).cpu_array.spec_index(cpu_id).view().view().current_process
                == Some(process_ptr),
            old(kernel).cpu_array.spec_index(cpu_id).view().view().current_thread
                == Some(current_thread_ptr),
            old(kernel).thread_map.spec_index(current_thread_ptr).view().state
                == (ThreadState::RUNNING { cpu_id }),
            old(kernel).thread_map.spec_index(current_thread_ptr).view().owning_proc
                == process_ptr,
            old(kernel).thread_map.spec_index(current_thread_ptr).view()
                .endpoint_descriptors.wf(),
            old(kernel).thread_map.spec_index(current_thread_ptr).view()
                .endpoint_descriptors.spec_index(endpoint_index)
                == Some(endpoint_ptr),
            old(kernel).thread_map.spec_index(current_thread_ptr).view()
                .free_quota_pending_clean(),
            old(kernel).thread_map.spec_index(current_thread_ptr).view()
                .temp_alloc_clean(),
            old(lctx).lock_id_set() =~= set![
                (
                    old(kernel).cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id),
                ),
                (
                    old(kernel).process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr),
                ),
                (
                    old(kernel).thread_map.lock_id_by_key(current_thread_ptr),
                    KernelObjId::Thread(current_thread_ptr),
                ),
                (
                    old(kernel).endpoint_map.lock_id_by_key(endpoint_ptr),
                    KernelObjId::Endpoint(endpoint_ptr),
                ),
            ],
            waiting_state.is_endpoint_waiting(),
            waiting_state is RECEIVING_CALL ==>
                old(kernel).thread_map.spec_index(current_thread_ptr).view().caller is None,
            !old(kernel).endpoint_map.spec_index(endpoint_ptr).view().queue.view()
                .contains(current_thread_ptr),
            old(kernel).endpoint_map.spec_index(endpoint_ptr).view().queue.len() == 0
                || match old(kernel).endpoint_map.spec_index(endpoint_ptr)
                    .view().queue_state {
                    EndpointState::SEND => waiting_state.is_endpoint_send_waiting(),
                    EndpointState::RECEIVE => waiting_state.is_endpoint_receive_waiting(),
                },
            cpu_objects_unlocked_except(
                old(kernel).cpu_array, old(lctx).thread_id(), set![cpu_id]),
            page_objects_unlocked(old(kernel).page_array, old(lctx).thread_id()),
            container_objects_unlocked(old(kernel).container_map, old(lctx).thread_id()),
            process_objects_unlocked_except(
                old(kernel).process_map, old(lctx).thread_id(), set![process_ptr]),
            thread_objects_unlocked_except(
                old(kernel).thread_map, old(lctx).thread_id(), set![current_thread_ptr]),
            endpoint_objects_unlocked_except(
                old(kernel).endpoint_map, old(lctx).thread_id(), set![endpoint_ptr]),
            pagetable_objects_unlocked(old(kernel).pagetable_map, old(lctx).thread_id()),
            iommu_table_objects_unlocked(old(kernel).iommu_table_map, old(lctx).thread_id()),
            scheduler_objects_unlocked(old(kernel).scheduler_map, old(lctx).thread_id()),
            pcid_allocator_objects_unlocked(
                old(kernel).pcid_allocator_map, old(lctx).thread_id()),
            allocator_objects_unlocked(old(kernel).allocator_4k_map, old(lctx).thread_id()),
            allocator_objects_unlocked(old(kernel).allocator_2m_map, old(lctx).thread_id()),
            allocator_objects_unlocked(old(kernel).allocator_1g_map, old(lctx).thread_id()),
            lock_id_aligned(old(kernel), old(lctx)),
        ensures
            ret is CpuIdle,
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(steps).steps.len() == old(steps).steps.len() + 1,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(kernel).all_objects_unlocked(final(lctx)),
            lock_id_aligned(final(kernel), final(lctx)),
    {
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked current_thread_lock_perm = current_thread_lock_perm.get();
        let tracked endpoint_lock_perm = endpoint_lock_perm.get();

        let ghost old_current_thread_lock_id =
            kernel.thread_map.lock_id_by_key(current_thread_ptr);
        proof {
            assert({
                &&& steps.snap_shot.cpu_array[cpu_id as int].state is Running
                &&& kernel.cpu_array.inv()
                &&& kernel.cpu_array.spec_index(cpu_id).view().is_init()
                &&& kernel.cpu_array.spec_index(cpu_id).view().view().wf()
            }) by {
                kernel.cpu_array.lemma_view_index(cpu_id);
                reveal(cpu_array_wf);
            };
        }

        let (endpoint_node_addr, endpoint_node_perm) =
            ipc_block_thread_on_endpoint(
                &mut kernel.thread_map, Tracked(&*lctx),
                current_thread_ptr, endpoint_ptr, endpoint_index,
                waiting_state, pt_regs, Tracked(&current_thread_lock_perm),
            );

        ipc_enqueue_endpoint_waiter(
            &mut kernel.endpoint_map, Tracked(&*lctx),
            endpoint_ptr, current_thread_ptr, waiting_state,
            endpoint_node_addr, endpoint_node_perm,
            Tracked(&endpoint_lock_perm),
        );

        let ghost old_cpu_lock_id =
            kernel.cpu_array.lock_id_by_index(cpu_id);
        let cpu_mut = kernel.cpu_array.borrow_mut(
            cpu_id, Tracked(&*lctx), Tracked(&cpu_lock_perm),
        );
        cpu_mut.block_current();

        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(
                KernelObjId::Thread(current_thread_ptr),
                old_current_thread_lock_id,
                kernel.thread_map.lock_id_by_key(current_thread_ptr),
            );
            lctx.update_lock_id(
                KernelObjId::Cpu(cpu_id),
                old_cpu_lock_id,
                kernel.cpu_array.lock_id_by_index(cpu_id),
            );
            assert(kernel.subsystems_inv()) by {
                assert({
                    &&& cpu_array_wf(
                        kernel.cpu_array, kernel.default_pagetable.view())
                    &&& thread_perms_wf(kernel.thread_map)
                    &&& endpoint_perms_wf(kernel.endpoint_map)
                }) by {
                    reveal(cpu_array_wf);
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
                assert(
                    thread_pages_wf(kernel.thread_map, kernel.page_array)
                    && endpoint_pages_wf(kernel.endpoint_map, kernel.page_array)
                ) by {
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
                assert(container_process_allocator_quota_4k_wf(
                    kernel.container_map, kernel.process_map,
                    kernel.thread_map, kernel.allocator_4k_map,
                )) by {
                    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(
                        kernel.container_map, kernel.process_map,
                        old(kernel).thread_map, kernel.thread_map,
                        kernel.allocator_4k_map,
                    );
                };
                assert(container_process_allocator_quota_2m_wf(
                    kernel.container_map, kernel.process_map,
                    kernel.thread_map, kernel.allocator_2m_map,
                )) by {
                    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(
                        kernel.container_map, kernel.process_map,
                        old(kernel).thread_map, kernel.thread_map,
                        kernel.allocator_2m_map,
                    );
                };
                assert(container_process_allocator_quota_1g_wf(
                    kernel.container_map, kernel.process_map,
                    kernel.thread_map, kernel.allocator_1g_map,
                )) by {
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(
                        kernel.container_map, kernel.process_map,
                        old(kernel).thread_map, kernel.thread_map,
                        kernel.allocator_1g_map,
                    );
                };
            };
            assert(kernel.process_management_inv()) by {
                assert({
                    &&& kernel.thread_map.spec_index(current_thread_ptr).view()
                        .endpoint_descriptors
                        == old(kernel).thread_map.spec_index(current_thread_ptr)
                            .view().endpoint_descriptors
                    &&& old(kernel).endpoint_map.spec_index(endpoint_ptr)
                        .view().queue.wf()
                }) by {
                    reveal(endpoint_perms_wf);
                    reveal(endpoints_inv);
                };
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
                    &&& container_thread_scheduler_wf(
                        kernel.container_map, kernel.thread_map, kernel.scheduler_map)
                    &&& container_thread_wf(
                        kernel.container_map, kernel.thread_map)
                    &&& process_thread_wf(
                        kernel.process_map, kernel.thread_map)
                }) by {
                    reveal(container_thread_scheduler_wf);
                    reveal(container_thread_wf);
                    reveal(process_thread_wf);
                };
                assert({
                    &&& container_cpu_wf(
                        kernel.container_map, kernel.cpu_array)
                    &&& process_cpu_wf(
                        kernel.process_map, kernel.cpu_array)
                    &&& thread_cpu_wf(
                        kernel.thread_map, kernel.cpu_array)
                }) by {
                    reveal(container_cpu_wf);
                    reveal(process_cpu_wf);
                    reveal(thread_cpu_wf);
                };
                assert(thread_endpoint_queue_wf(
                    kernel.thread_map, kernel.endpoint_map,
                )) by {
                    seq_push_lemma::<RwLockThreadPtr>();
                    reveal(thread_perms_wf);
                    reveal(endpoint_perms_wf);
                    reveal(endpoints_inv);
                    reveal(LinkedList::wf_value_list);
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
            };
            assert({
                &&& cpu_dirty_map_wf(
                    kernel.container_map, kernel.process_map, kernel.cpu_array,
                    kernel.cpu_tlb, kernel.pagetable_map)
                &&& tlb_wf_spec(
                    kernel.cpu_tlb, kernel.pagetable_map, kernel.cpu_array)
                &&& lock_id_aligned(kernel, &*lctx)
                &&& cpu_objects_unlocked_except(
                    kernel.cpu_array, lctx.thread_id(), set![cpu_id])
                &&& page_objects_unlocked(kernel.page_array, lctx.thread_id())
                &&& container_objects_unlocked(kernel.container_map, lctx.thread_id())
                &&& process_objects_unlocked_except(
                    kernel.process_map, lctx.thread_id(), set![process_ptr])
                &&& thread_objects_unlocked_except(
                    kernel.thread_map, lctx.thread_id(), set![current_thread_ptr])
                &&& endpoint_objects_unlocked_except(
                    kernel.endpoint_map, lctx.thread_id(), set![endpoint_ptr])
                &&& pagetable_objects_unlocked(kernel.pagetable_map, lctx.thread_id())
                &&& iommu_table_objects_unlocked(kernel.iommu_table_map, lctx.thread_id())
                &&& scheduler_objects_unlocked(kernel.scheduler_map, lctx.thread_id())
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
                reveal(lock_id_aligned);
                reveal(cpu_objects_unlocked_except);
                reveal(process_objects_unlocked_except);
                reveal(thread_objects_unlocked_except);
                reveal(endpoint_objects_unlocked_except);
            };
        }

        kernel.wunlock_endpoint(
            endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm),
        );
        kernel.wunlock_thread(
            current_thread_ptr, Tracked(&mut *lctx),
            Tracked(current_thread_lock_perm),
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
                &&& steps.snap_shot.cpu_array[cpu_id as int].state
                    != kernel_k_to_kernel_u(*kernel)
                        .cpu_array[cpu_id as int].state
            }) by {
                reveal(cpu_objects_unlocked_except);
                reveal(process_objects_unlocked_except);
                reveal(thread_objects_unlocked_except);
                reveal(endpoint_objects_unlocked_except);
                kernel.cpu_array.lemma_view_index(cpu_id);
            };
            steps.end_kernel_step(&*kernel, &*lctx);
        }
        RetValueType::CpuIdle
    }

} // verus!
