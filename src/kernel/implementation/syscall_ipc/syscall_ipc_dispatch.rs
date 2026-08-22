use vstd::prelude::*;
use vstd::assert_sets_equal;
use crate::*;
use super::syscall_ipc_transition::{
    ipc_block_current, ipc_match_ordinary,
    ipc_release_current_endpoint_and_finish,
};
#[cfg(not(feature = "ipc-pilot"))]
use crate::implementation::syscall_new_thread::syscall_new_thread_helpers::
    new_thread_other_objects_unlocked;
#[cfg(feature = "ipc-pilot")]
use veriflat_kernel_core::kernel::implementation::ipc_release_helpers::
    new_thread_other_objects_unlocked;

verus! {

    pub(super) fn syscall_ipc_ordinary_empty(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
        waiting_state: ThreadState,
        pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            edp_idx_valid(endpoint_index),
            waiting_state is SENDING || waiting_state is RECEIVING,
            old(kernel).inv(),
            old(kernel).cpu_array.spec_index(cpu_id).view().view().state
                is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            old(steps).steps.len() == 0,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            old(kernel).all_objects_unlocked(old(lctx)),
            lock_id_aligned(old(kernel), old(lctx)),
        ensures
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(kernel).all_objects_unlocked(final(lctx)),
            lock_id_aligned(final(kernel), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle ==> final(steps).steps.len() == 1,
            !(ret is CpuIdle) ==> final(steps).steps.len() == 0,
            ret is Success
                || ret is CpuIdle
                || ret is ErrorProcessKilled
                || ret is ErrorThreadKilled
                || ret is ErrorInvalidEndpoint
                || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch,
    {
        let Tracked(cpu_lock_perm) =
            kernel.wlock_cpu(cpu_id, Tracked(&mut *lctx));
        let cpu_ref = kernel.cpu_array.borrow(
            cpu_id, Tracked(&cpu_lock_perm),
        );
        let process_ptr = cpu_ref.current_process.unwrap();
        let current_thread_ptr = cpu_ref.current_thread.unwrap();

        proof {
            assert({
                &&& kernel.process_map.dom().contains(process_ptr)
                &&& kernel.process_map.lock_id_by_key(process_ptr)
                    .spec_gt(kernel.cpu_array.lock_id_by_index(cpu_id))
            }) by {
                reveal(container_cpu_wf);
                reveal(process_cpu_wf);
                reveal(container_process_wf);
                reveal(process_perms_wf);
            };
        }
        let process_res = kernel.wlock_process_unless_killed(
            process_ptr, Tracked(&mut *lctx),
        );
        if let (false, _) = process_res {
            proof {
                assert(
                    steps.snap_shot == kernel_k_to_kernel_u(*kernel)
                    && new_thread_other_objects_unlocked(
                        kernel, lctx.thread_id(), Some(cpu_id),
                        None, None, None, None,
                    )
                ) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                        old(kernel), kernel,
                    );
                    reveal(new_thread_other_objects_unlocked);
                };
            }
            kernel.release_cpu_and_finish(
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
                Tracked(cpu_lock_perm),
            );
            return RetValueType::ErrorProcessKilled;
        }
        let Tracked(process_lock_perm) = process_res.1.unwrap();

        proof {
            assert({
                &&& kernel.thread_map.dom().contains(current_thread_ptr)
                &&& kernel.thread_map.spec_index(current_thread_ptr).view().state
                    == (ThreadState::RUNNING { cpu_id })
                &&& kernel.thread_map.spec_index(current_thread_ptr).view()
                    .owning_proc == process_ptr
                &&& kernel.thread_map.spec_index(current_thread_ptr).view()
                    .owning_container
                    == kernel.process_map.spec_index(process_ptr)
                        .view_rodata().view().owning_container
                &&& kernel.thread_map.spec_index(current_thread_ptr).view()
                    .container_depth
                    == kernel.process_map.spec_index(process_ptr)
                        .view_rodata().view().container_depth
                &&& kernel.thread_map.spec_index(current_thread_ptr).view()
                    .process_depth
                    == kernel.process_map.spec_index(process_ptr)
                        .view_rodata().view().depth
                &&& kernel.thread_map.lock_id_by_key(current_thread_ptr)
                    .spec_gt(kernel.process_map.lock_id_by_key(process_ptr))
            }) by {
                reveal(thread_cpu_wf);
                reveal(process_thread_wf);
                reveal(process_perms_wf);
                reveal(thread_perms_wf);
            };
        }
        let current_thread_res = kernel.wlock_thread_unless_killed(
            current_thread_ptr, Tracked(&mut *lctx),
        );
        if let (false, _) = current_thread_res {
            proof {
                assert(
                    steps.snap_shot == kernel_k_to_kernel_u(*kernel)
                    && new_thread_other_objects_unlocked(
                        kernel, lctx.thread_id(), Some(cpu_id),
                        None, Some(process_ptr), None, None,
                    )
                ) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                        old(kernel), kernel,
                    );
                    reveal(new_thread_other_objects_unlocked);
                };
            }
            kernel.release_cpu_and_process_and_finish(
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
                process_ptr, Tracked(process_lock_perm),
                Tracked(cpu_lock_perm),
            );
            return RetValueType::ErrorThreadKilled;
        }
        let Tracked(current_thread_lock_perm) =
            current_thread_res.1.unwrap();

        let current_thread_ref = kernel.thread_map.borrow(
            current_thread_ptr, Tracked(&current_thread_lock_perm),
        );
        let endpoint_option =
            *current_thread_ref.endpoint_descriptors.get(endpoint_index);
        if let None = endpoint_option {
            proof {
                assert(
                    steps.snap_shot == kernel_k_to_kernel_u(*kernel)
                    && new_thread_other_objects_unlocked(
                        kernel, lctx.thread_id(), Some(cpu_id),
                        None, Some(process_ptr),
                        Some(current_thread_ptr), None,
                    )
                ) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                        old(kernel), kernel,
                    );
                    reveal(new_thread_other_objects_unlocked);
                };
            }
            kernel.release_cpu_and_process_and_thread_and_finish(
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
                process_ptr, current_thread_ptr,
                Tracked(current_thread_lock_perm),
                Tracked(process_lock_perm), Tracked(cpu_lock_perm),
            );
            return RetValueType::ErrorInvalidEndpoint;
        }
        let endpoint_ptr = endpoint_option.unwrap();

        proof {
            assert({
                &&& kernel.endpoint_map.dom().contains(endpoint_ptr)
                &&& current_thread_lock_perm.ordering_lock_id().major
                    == THREAD_LOCK_MAJOR
                &&& kernel.endpoint_map.lock_id_by_key(endpoint_ptr).major
                    == ENDPOINT_LOCK_MAJOR
                &&& new_thread_other_objects_unlocked(
                    kernel, lctx.thread_id(), Some(cpu_id),
                    None, Some(process_ptr), Some(current_thread_ptr), None,
                )
                &&& steps.snap_shot == kernel_k_to_kernel_u(*kernel)
            }) by {
                reveal(thread_endpoint_ref_counter_wf);
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
                reveal(new_thread_other_objects_unlocked);
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                    old(kernel), kernel,
                );
            };
            assert(lctx.lock_id_acyclic(
                kernel.endpoint_map.lock_id_by_key(endpoint_ptr),
            )) by {
                reveal(process_perms_wf);
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
            };
        }
        let Tracked(endpoint_lock_perm) = kernel.wlock_endpoint(
            endpoint_ptr, Tracked(&mut *lctx),
        );

        proof {
            assert({
                &&& kernel.endpoint_map.perms_wf()
                &&& kernel.thread_map.spec_index(current_thread_ptr).view().state
                    == (ThreadState::RUNNING { cpu_id })
            }) by {
                reveal(endpoint_perms_wf);
                reveal(thread_cpu_wf);
            };
        }
        let endpoint_ref = kernel.endpoint_map.borrow(
            endpoint_ptr, Tracked(&endpoint_lock_perm),
        );
        let queue_len = endpoint_ref.queue.len();
        let queue_is_send = endpoint_ref.queue_state.is_send();
        let waiting_is_send = match waiting_state {
            ThreadState::SENDING => true,
            _ => false,
        };

        if queue_len == 0 || queue_is_send == waiting_is_send {
            proof {
                assert_sets_equal!(lctx.lock_id_set() == set![
                    (
                        kernel.cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id),
                    ),
                    (
                        kernel.process_map.lock_id_by_key(process_ptr),
                        KernelObjId::Process(process_ptr),
                    ),
                    (
                        kernel.thread_map.lock_id_by_key(current_thread_ptr),
                        KernelObjId::Thread(current_thread_ptr),
                    ),
                    (
                        kernel.endpoint_map.lock_id_by_key(endpoint_ptr),
                        KernelObjId::Endpoint(endpoint_ptr),
                    ),
                ], held => {});
                assert({
                    &&& !kernel.endpoint_map.spec_index(endpoint_ptr).view()
                        .queue.view().contains(current_thread_ptr)
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
                    reveal(thread_endpoint_queue_wf);
                    reveal(cpu_objects_unlocked_except);
                    reveal(process_objects_unlocked_except);
                    reveal(thread_objects_unlocked_except);
                    reveal(endpoint_objects_unlocked_except);
                };
            }
            return ipc_block_current(kernel, 
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
                process_ptr, current_thread_ptr, endpoint_ptr,
                endpoint_index, waiting_state, &*pt_regs,
                Tracked(cpu_lock_perm), Tracked(process_lock_perm),
                Tracked(current_thread_lock_perm),
                Tracked(endpoint_lock_perm),
            );
        }

        proof {
            assert(
                kernel.endpoint_map.spec_index(endpoint_ptr).view().queue.wf()
            ) by {
                reveal(endpoint_perms_wf);
                reveal(endpoints_inv);
            };
        }
        let (_, peer_thread_ptr) = endpoint_ref.queue.peek_head();

        proof {
            assert_sets_equal!(lctx.lock_id_set() == set![
                (
                    kernel.cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id),
                ),
                (
                    kernel.process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr),
                ),
                (
                    kernel.thread_map.lock_id_by_key(current_thread_ptr),
                    KernelObjId::Thread(current_thread_ptr),
                ),
                (
                    kernel.endpoint_map.lock_id_by_key(endpoint_ptr),
                    KernelObjId::Endpoint(endpoint_ptr),
                ),
            ], held => {});
            assert({
                &&& kernel.thread_map.dom().contains(peer_thread_ptr)
                &&& kernel.thread_map.spec_index(peer_thread_ptr).view()
                    .state.is_endpoint_waiting()
                &&& kernel.thread_map.spec_index(peer_thread_ptr).view()
                    .blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& peer_thread_ptr != current_thread_ptr
                &&& !kernel.thread_map.spec_index(peer_thread_ptr)
                    .wlocked_by(&*lctx)
                &&& kernel.thread_map.lock_id_by_key(peer_thread_ptr).major
                    == THREAD_BLOCKED_LOCK_MAJOR
                &&& lctx.lock_id_acyclic(
                    kernel.thread_map.lock_id_by_key(peer_thread_ptr))
            }) by {
                reveal(process_perms_wf);
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
                reveal(thread_endpoint_queue_wf);
                reveal(thread_cpu_wf);
                reveal(thread_objects_unlocked_except);
            };
        }
        let peer_thread_res = kernel.wlock_thread_unless_killed(
            peer_thread_ptr, Tracked(&mut *lctx),
        );
        if let (false, _) = peer_thread_res {
            proof {
                assert({
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
                    reveal(cpu_objects_unlocked_except);
                    reveal(process_objects_unlocked_except);
                    reveal(thread_objects_unlocked_except);
                    reveal(endpoint_objects_unlocked_except);
                };
            }
            return ipc_release_current_endpoint_and_finish(kernel, 
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
                process_ptr, current_thread_ptr, endpoint_ptr,
                RetValueType::ErrorIpcPeerKilled,
                Tracked(cpu_lock_perm), Tracked(process_lock_perm),
                Tracked(current_thread_lock_perm),
                Tracked(endpoint_lock_perm),
            );
        }
        let Tracked(peer_thread_lock_perm) =
            peer_thread_res.1.unwrap();
        let peer_thread_ref = kernel.thread_map.borrow(
            peer_thread_ptr, Tracked(&peer_thread_lock_perm),
        );
        let compatible = match (
            waiting_state, peer_thread_ref.state, peer_thread_ref.ipc_payload,
        ) {
            (ThreadState::SENDING, ThreadState::RECEIVING, IPCPayLoad::Empty) => true,
            (ThreadState::RECEIVING, ThreadState::SENDING, IPCPayLoad::Empty) => true,
            _ => false,
        };
        if !compatible {
            kernel.wunlock_thread(
                peer_thread_ptr, Tracked(&mut *lctx),
                Tracked(peer_thread_lock_perm),
            );
            proof {
                assert({
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
                    reveal(thread_objects_unlocked_except);
                };
            }
            return ipc_release_current_endpoint_and_finish(kernel, 
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
                process_ptr, current_thread_ptr, endpoint_ptr,
                RetValueType::ErrorIpcTypeMismatch,
                Tracked(cpu_lock_perm), Tracked(process_lock_perm),
                Tracked(current_thread_lock_perm),
                Tracked(endpoint_lock_perm),
            );
        }

        let peer_container_ptr = peer_thread_ref.owning_container;
        proof {
            assert(
                kernel.container_map.dom().contains(peer_container_ptr)
                && kernel.container_map.perms_wf()
            ) by {
                reveal(container_thread_wf);
                reveal(container_perms_wf);
            };
        }
        let peer_scheduler_ptr = kernel.container_map
            .borrow_rodata(peer_container_ptr).borrow().scheduler;
        proof {
            assert({
                &&& kernel.scheduler_map.dom().contains(peer_scheduler_ptr)
                &&& kernel.scheduler_map.lock_id_by_key(peer_scheduler_ptr).major
                    == SCHEDULER_LOCK_MAJOR
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
                &&& scheduler_objects_unlocked(kernel.scheduler_map, lctx.thread_id())
                &&& !kernel.scheduler_map.spec_index(peer_scheduler_ptr)
                    .locked_by_thread(lctx.thread_id())
                &&& pcid_allocator_objects_unlocked(
                    kernel.pcid_allocator_map, lctx.thread_id())
                &&& allocator_objects_unlocked(kernel.allocator_4k_map, lctx.thread_id())
                &&& allocator_objects_unlocked(kernel.allocator_2m_map, lctx.thread_id())
                &&& allocator_objects_unlocked(kernel.allocator_1g_map, lctx.thread_id())
            }) by {
                reveal(container_scheduler_wf);
                reveal(scheduler_perms_wf);
                reveal(cpu_objects_unlocked_except);
                reveal(process_objects_unlocked_except);
                reveal(thread_objects_unlocked_except);
                reveal(endpoint_objects_unlocked_except);
            };
            assert(lctx.lock_id_acyclic(
                kernel.scheduler_map.lock_id_by_key(peer_scheduler_ptr),
            )) by {
                reveal(process_perms_wf);
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
                reveal(scheduler_perms_wf);
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
                reveal(container_scheduler_wf);
                reveal(container_thread_scheduler_wf);
                reveal(cpu_objects_unlocked_except);
                reveal(process_objects_unlocked_except);
                reveal(thread_objects_unlocked_except);
                reveal(endpoint_objects_unlocked_except);
                reveal(scheduler_objects_unlocked_except);
            };
        }
        ipc_match_ordinary(kernel, 
            Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            process_ptr, current_thread_ptr, endpoint_ptr,
            peer_thread_ptr, peer_scheduler_ptr,
            Tracked(cpu_lock_perm), Tracked(process_lock_perm),
            Tracked(current_thread_lock_perm),
            Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
            Tracked(peer_scheduler_lock_perm),
        )
    }


} // verus!
