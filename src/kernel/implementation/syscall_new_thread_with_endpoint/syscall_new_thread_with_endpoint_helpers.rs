use vstd::prelude::*;
use crate::*;
use super::super::syscall_new_thread::syscall_new_thread_helpers::{
    create_thread_from_staged_page_merged,
    kernel_u_new_thread_changed,
};

verus! {


    pub(super) fn add_new_thread_with_endpoint(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        process_ptr: RwLockProcessPtr,
        current_thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        scheduler_ptr: RwLockSchedulerPtr,
        endpoint_ptr: RwLockEndpointPtr,
        endpoint_index: EndpointIdx,
        process_lock_perm: Tracked<LockPerm>,
        current_thread_lock_perm: Tracked<LockPerm>,
        cpu_lock_perm: Tracked<LockPerm>,
        scheduler_lock_perm: Tracked<LockPerm>,
        endpoint_lock_perm: Tracked<LockPerm>,
    )
        requires
            index_valid(NUM_CPUS, cpu_id),
            edp_idx_valid(endpoint_index),
            old(kernel).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            old(kernel).scheduler_map.dom().contains(scheduler_ptr),
            old(kernel).process_map.dom().contains(process_ptr),
            old(kernel).thread_map.dom().contains(current_thread_ptr),
            old(kernel).container_map.dom().contains(container_ptr),
            old(kernel).endpoint_map.dom().contains(endpoint_ptr),
            old(kernel).thread_map.spec_index(current_thread_ptr).view()
                .endpoint_descriptors.wf(),
            old(kernel).container_map.dom().contains(
                old(kernel).endpoint_map.spec_index(endpoint_ptr).view().owning_container,
            ),
            old(kernel).thread_map.spec_index(current_thread_ptr).view()
                .endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
            {
                ||| old(kernel).endpoint_map.spec_index(endpoint_ptr).view().owning_container
                    == container_ptr
                ||| old(kernel).container_map.spec_index(
                        old(kernel).endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                    ).view().subtree_set.view().contains(container_ptr)
            },
            old(lctx).lock_id_set() =~= set![
                (old(kernel).cpu_array.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id)),
                (old(kernel).scheduler_map.lock_id_by_key(scheduler_ptr),
                    KernelObjId::Scheduler(scheduler_ptr)),
                (old(kernel).process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr)),
                (old(kernel).thread_map.lock_id_by_key(current_thread_ptr),
                    KernelObjId::Thread(current_thread_ptr)),
                (old(kernel).endpoint_map.lock_id_by_key(endpoint_ptr),
                    KernelObjId::Endpoint(endpoint_ptr)),
            ],
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id()
                == old(kernel).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(kernel).cpu_array.spec_index(cpu_id).view().being_killed() == false,
            old(kernel).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
            scheduler_lock_perm.view().state() is WriteLock,
            scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
            scheduler_lock_perm.view().lock_id()
                == old(kernel).scheduler_map.spec_index(scheduler_ptr)
                    .locking_thread()->Write_lock_id,
            scheduler_lock_perm.view().ordering_lock_id().major
                == SCHEDULER_LOCK_MAJOR,
            old(kernel).scheduler_map.spec_index(scheduler_ptr).wlocked_by(old(lctx)),
            old(kernel).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
            old(kernel).container_map.spec_index(container_ptr).view_rodata().view().scheduler
                == scheduler_ptr,
            endpoint_lock_perm.view().state() is WriteLock,
            endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.view().lock_id()
                == old(kernel).endpoint_map.spec_index(endpoint_ptr)
                    .locking_thread()->Write_lock_id,
            endpoint_lock_perm.view().ordering_lock_id().major
                == ENDPOINT_LOCK_MAJOR,
            old(kernel).endpoint_map.spec_index(endpoint_ptr).wlocked_by(old(lctx)),
            old(kernel).endpoint_map.spec_index(endpoint_ptr).being_killed() == false,
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id()
                == old(kernel).process_map.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            process_lock_perm.view().ordering_lock_id().major
                == PROCESS_LOCK_MAJOR,
            old(kernel).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(kernel).process_map.spec_index(process_ptr).being_killed() == false,
            old(kernel).process_map.spec_index(process_ptr).view_rodata().view().owning_container
                == container_ptr,
            current_thread_lock_perm.view().state() is WriteLock,
            current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.view().lock_id()
                == old(kernel).thread_map.spec_index(current_thread_ptr)
                    .locking_thread()->Write_lock_id,
            current_thread_lock_perm.view().ordering_lock_id().major
                == THREAD_LOCK_MAJOR,
            old(kernel).thread_map.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
            old(kernel).thread_map.spec_index(current_thread_ptr).being_killed() == false,
            old(kernel).thread_map.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
            old(kernel).thread_map.spec_index(current_thread_ptr).view().owning_container
                == container_ptr,
            old(kernel).thread_map.spec_index(current_thread_ptr).view().temp_alloc_clean(),
            old(kernel).thread_map.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
            old(kernel).thread_map.spec_index(current_thread_ptr).view().quota_4k >= 1,
            old(kernel).thread_map.lock_id_by_key(current_thread_ptr).major == THREAD_LOCK_MAJOR,
            kernel_objects_unlocked_except(
                old(kernel), old(lctx).thread_id(), Some(cpu_id),
                Some(scheduler_ptr), Some(process_ptr),
                Some(current_thread_ptr), Some(endpoint_ptr)),
            lock_id_aligned(old(kernel), old(lctx)),
        ensures
            lock_id_aligned(final(kernel), final(lctx)),
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            !final(kernel).cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(final(lctx).thread_id()),
            !final(kernel).scheduler_map.spec_index(scheduler_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            !final(kernel).process_map.spec_index(process_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            !final(kernel).thread_map.spec_index(current_thread_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            !final(kernel).endpoint_map.spec_index(endpoint_ptr)
                .locked_by_thread(final(lctx).thread_id()),
            final(kernel).all_objects_unlocked(final(lctx)),
            final(steps).steps.len() == old(steps).steps.len() + 1,
            final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(kernel)),
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            kernel_u_new_thread_changed(
                final(steps).steps.last().old_u,
                final(steps).steps.last().new_u,
                process_ptr,
            ),
    {
        let tracked mut process_lock_perm = process_lock_perm.get();
        let tracked mut current_thread_lock_perm = current_thread_lock_perm.get();
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        let tracked scheduler_lock_perm = scheduler_lock_perm.get();
        let tracked endpoint_lock_perm = endpoint_lock_perm.get();

        proof {
            assert({
                &&& kernel.cpu_array.lock_id_by_index(cpu_id).major
                    == CPU_LOCK_MAJOR_RUNNING
                &&& kernel.scheduler_map.lock_id_by_key(scheduler_ptr).major
                    == SCHEDULER_LOCK_MAJOR
                &&& kernel.process_map.lock_id_by_key(process_ptr).major
                    == PROCESS_LOCK_MAJOR
                &&& kernel.endpoint_map.lock_id_by_key(endpoint_ptr).major
                    == ENDPOINT_LOCK_MAJOR
            }) by {
                reveal(cpu_array_wf);
                reveal(scheduler_perms_wf);
                reveal(process_perms_wf);
                reveal(endpoint_perms_wf);
            };
        }

        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(kernel,
            current_thread_ptr, container_ptr, cpu_id,
            Tracked(&mut *lctx), Tracked(&mut *steps),
            Tracked(&current_thread_lock_perm),
        );
        let page_index = page_ptr2page_index(page_ptr);

        proof {
            assert(endpoint_objects_unlocked_except(
                kernel.endpoint_map, lctx.thread_id(), set![endpoint_ptr],
            )) by {
                endpoint_objects_unlocked_except_preserved_for_held_unchanged(
                    old(kernel).endpoint_map, kernel.endpoint_map, &*lctx,
                    set![endpoint_ptr],
                );
            };
            assert(page_ptr != current_thread_ptr) by {
                reveal(thread_pages_wf);
            };
        }

        proof {
            assert({
                &&& kernel.container_map.dom().contains(container_ptr)
                &&& kernel.container_map.spec_index(container_ptr)
                    .view_rodata().view().scheduler == scheduler_ptr
            }) by {
                reveal(container_scheduler_wf);
            };
            enter_kernel_view_release_preserving_lock_id_alignment(
                &*kernel, &mut *lctx,
            );
            assert(kernel.container_map.dom().contains(
                kernel.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
            )) by {
                reveal(container_endpoint_wf);
            };
            assert({
                ||| kernel.endpoint_map.spec_index(endpoint_ptr).view().owning_container
                    == container_ptr
                ||| kernel.container_map.spec_index(
                        kernel.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                    ).view().subtree_set.view().contains(container_ptr)
            }) by {
                reveal(container_thread_endpoint_wf);
            };
        }
        let (new_thread_ptr, Tracked(new_thread_lock_perm)) =
            create_thread_from_staged_page_merged(kernel,
                page_ptr, process_ptr, current_thread_ptr, container_ptr, scheduler_ptr,
                Tracked(&mut *lctx), Tracked(&page_lock_perm),
                Tracked(&process_lock_perm), Tracked(&current_thread_lock_perm),
                Tracked(&scheduler_lock_perm),
            );

        proof {
            assert(kernel.container_map.dom().contains(
                kernel.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
            )) by {
                reveal(container_endpoint_wf);
            };
            assert(kernel.thread_map.lock_id_by_key(new_thread_ptr)
                != kernel.thread_map.lock_id_by_key(current_thread_ptr)) by {
                reveal(thread_perms_wf);
                reveal(thread_cpu_wf);
            };
        }
        proof {
            assert(kernel.endpoint_map.spec_index(endpoint_ptr).is_init()) by {
                reveal(endpoint_perms_wf);
                reveal(endpoints_inv);
            };
        }
        attach_endpoint_reference_and_unlock(kernel,
            new_thread_ptr, endpoint_ptr, cpu_id, scheduler_ptr, process_ptr,
            current_thread_ptr, page_index, Tracked(&mut *lctx),
            Tracked(new_thread_lock_perm), Tracked(endpoint_lock_perm),
            Ghost(kernel.scheduler_map.lock_id_by_key(scheduler_ptr)),
            Ghost(kernel.process_map.lock_id_by_key(process_ptr)),
            Ghost(kernel.thread_map.lock_id_by_key(current_thread_ptr)),
        );
        kernel.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
        kernel.wunlock_scheduler(
            scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm),
        );
        kernel.wunlock_thread(
            current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm),
        );
        kernel.wunlock_process(
            process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm),
        );
        kernel.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

        proof {
            steps.end_kernel_step(&*kernel, &*lctx);
        }
    }

    /// Add the first endpoint descriptor and its reverse reference together.
    fn attach_endpoint_reference_and_unlock(
        kernel: &mut KernelK,
        thread_ptr: RwLockThreadPtr,
        endpoint_ptr: RwLockEndpointPtr,
        cpu_id: CpuId,
        scheduler_ptr: RwLockSchedulerPtr,
        process_ptr: RwLockProcessPtr,
        current_thread_ptr: RwLockThreadPtr,
        page_index: PageIndex,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(thread_lock_perm): Tracked<LockPerm>,
        Tracked(endpoint_lock_perm): Tracked<LockPerm>,
        scheduler_lock_id: Ghost<LockId>,
        process_lock_id: Ghost<LockId>,
        current_thread_lock_id: Ghost<LockId>,
    )
        requires
            old(kernel).inv(),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_PAGES, page_index),
            old(kernel).scheduler_map.dom().contains(scheduler_ptr),
            old(kernel).process_map.dom().contains(process_ptr),
            old(kernel).thread_map.dom().contains(current_thread_ptr),
            current_thread_ptr != thread_ptr,
            old(kernel).thread_map.dom().contains(thread_ptr),
            old(kernel).thread_map.spec_index(thread_ptr).is_init(),
            old(kernel).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(kernel).thread_map.spec_index(thread_ptr).view().state is SCHEDULED,
            old(kernel).thread_map.spec_index(thread_ptr).view().endpoint_descriptors.wf(),
            old(kernel).thread_map.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(kernel).thread_map.spec_index(thread_ptr).view()
                .endpoint_descriptors.spec_index(0) is None,
            old(kernel).endpoint_map.dom().contains(endpoint_ptr),
            old(kernel).endpoint_map.spec_index(endpoint_ptr).is_init(),
            old(kernel).container_map.dom().contains(
                old(kernel).endpoint_map.spec_index(endpoint_ptr).view().owning_container,
            ),
            {
                ||| old(kernel).endpoint_map.spec_index(endpoint_ptr).view().owning_container
                    == old(kernel).thread_map.spec_index(thread_ptr).view().owning_container
                ||| old(kernel).container_map.spec_index(
                        old(kernel).endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                    ).view().subtree_set.view().contains(
                        old(kernel).thread_map.spec_index(thread_ptr).view().owning_container,
                    )
            },
            old(kernel).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id()
                == old(kernel).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            old(kernel).endpoint_map.spec_index(endpoint_ptr).wlocked_by(old(lctx)),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id()
                == old(kernel).endpoint_map.spec_index(endpoint_ptr)
                    .locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).lock_id_set() =~= set![
                (old(kernel).cpu_array.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id)),
                (old(kernel).page_array.lock_id_by_index(page_index), KernelObjId::Page(page_index)),
                (scheduler_lock_id.view(), KernelObjId::Scheduler(scheduler_ptr)),
                (process_lock_id.view(), KernelObjId::Process(process_ptr)),
                (current_thread_lock_id.view(), KernelObjId::Thread(current_thread_ptr)),
                (old(kernel).endpoint_map.lock_id_by_key(endpoint_ptr),
                    KernelObjId::Endpoint(endpoint_ptr)),
                (old(kernel).thread_map.lock_id_by_key(thread_ptr),
                    KernelObjId::Thread(thread_ptr)),
            ],
            old(lctx).lock_entry_contains(
                old(kernel).thread_map.lock_id_by_key(thread_ptr),
                KernelObjId::Thread(thread_ptr)),
            old(lctx).lock_entry_contains(
                old(kernel).endpoint_map.lock_id_by_key(endpoint_ptr),
                KernelObjId::Endpoint(endpoint_ptr)),
            lock_id_aligned(old(kernel), old(lctx)),
            thread_objects_unlocked_except(
                old(kernel).thread_map, old(lctx).thread_id(),
                set![current_thread_ptr, thread_ptr]),
            endpoint_objects_unlocked_except(
                old(kernel).endpoint_map, old(lctx).thread_id(), set![endpoint_ptr]),
        ensures
            final(kernel).inv(),
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .endpoint_descriptors.spec_index(0) == Some(endpoint_ptr),
            final(kernel).endpoint_map.spec_index(endpoint_ptr).view().owning_threads
                .view().contains((thread_ptr, 0)),
            final(kernel).endpoint_map.spec_index(endpoint_ptr).view().rf_counter
                == old(kernel).endpoint_map.spec_index(endpoint_ptr).view().rf_counter + 1,
            final(kernel).thread_map.spec_index(thread_ptr).being_killed()
                == old(kernel).thread_map.spec_index(thread_ptr).being_killed(),
            final(kernel).thread_map.spec_index(thread_ptr).view().state
                == old(kernel).thread_map.spec_index(thread_ptr).view().state,
            final(kernel).thread_map.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(kernel).thread_map.spec_index(thread_ptr).locking_thread() is None,
            final(kernel).endpoint_map.spec_index(endpoint_ptr).locking_thread() is None,
            final(kernel).thread_map.lock_id_by_key(thread_ptr)
                == old(kernel).thread_map.lock_id_by_key(thread_ptr),
            final(kernel).endpoint_map.lock_id_by_key(endpoint_ptr)
                == old(kernel).endpoint_map.lock_id_by_key(endpoint_ptr),
            final(kernel).thread_map.unchanged_except(&old(kernel).thread_map, thread_ptr),
            final(kernel).thread_map.spec_index(current_thread_ptr)
                == old(kernel).thread_map.spec_index(current_thread_ptr),
            final(kernel).endpoint_map.unchanged_except(&old(kernel).endpoint_map, endpoint_ptr),
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
            final(kernel).cpu_array.lock_id_by_index(cpu_id)
                == old(kernel).cpu_array.lock_id_by_index(cpu_id),
            final(kernel).scheduler_map.lock_id_by_key(scheduler_ptr)
                == old(kernel).scheduler_map.lock_id_by_key(scheduler_ptr),
            final(kernel).process_map.lock_id_by_key(process_ptr)
                == old(kernel).process_map.lock_id_by_key(process_ptr),
            final(kernel).thread_map.lock_id_by_key(current_thread_ptr)
                == old(kernel).thread_map.lock_id_by_key(current_thread_ptr),
            final(kernel).page_array.lock_id_by_index(page_index)
                == old(kernel).page_array.lock_id_by_index(page_index),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() == old(lctx).lock_id_set()
                .remove((
                    old(kernel).thread_map.lock_id_by_key(thread_ptr),
                    KernelObjId::Thread(thread_ptr),
                ))
                .remove((
                    old(kernel).endpoint_map.lock_id_by_key(endpoint_ptr),
                    KernelObjId::Endpoint(endpoint_ptr),
                )),
            final(lctx).lock_id_set() =~= set![
                (old(kernel).cpu_array.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id)),
                (old(kernel).page_array.lock_id_by_index(page_index), KernelObjId::Page(page_index)),
                (scheduler_lock_id.view(), KernelObjId::Scheduler(scheduler_ptr)),
                (process_lock_id.view(), KernelObjId::Process(process_ptr)),
                (current_thread_lock_id.view(), KernelObjId::Thread(current_thread_ptr)),
            ],
            lock_id_aligned(final(kernel), final(lctx)),
            thread_objects_unlocked_except(
                final(kernel).thread_map, final(lctx).thread_id(),
                set![current_thread_ptr]),
            endpoint_objects_unlocked(
                final(kernel).endpoint_map, final(lctx).thread_id()),
            kernel_k_to_kernel_u(*final(kernel)) == kernel_k_to_kernel_u(*old(kernel)),
    {
        proof {
            assert({
                &&& kernel.thread_map.view().spec_index(thread_ptr).is_init()
                &&& kernel.thread_map.view().spec_index(thread_ptr).addr()
                    == thread_ptr
                &&& kernel.endpoint_map.view().spec_index(endpoint_ptr).is_init()
                &&& kernel.endpoint_map.view().spec_index(endpoint_ptr).addr()
                    == endpoint_ptr
                &&& kernel.thread_map.spec_index(thread_ptr).view()
                    .endpoint_descriptors.wf()
                &&& kernel.endpoint_map.spec_index(endpoint_ptr).inv()
            }) by {
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
                reveal(endpoints_inv);
            };
            assert({
                &&& !kernel.endpoint_map.spec_index(endpoint_ptr).view()
                    .owning_threads.view().contains((thread_ptr, 0))
                &&& kernel.endpoint_map.spec_index(endpoint_ptr).view().rf_counter
                    < usize::MAX
            }) by {
                reveal(thread_endpoint_ref_counter_wf);
                endpoint_ref_counter_bounded(&*kernel, endpoint_ptr);
            };
        }
        {
            let thread_mut = kernel.thread_map.borrow_mut(
                thread_ptr, Tracked(&*lctx), Tracked(&thread_lock_perm),
            );
            thread_mut.endpoint_descriptors.set(0, Some(endpoint_ptr));
        }
        {
            let endpoint_mut = kernel.endpoint_map.borrow_mut(
                endpoint_ptr, Tracked(&*lctx), Tracked(&endpoint_lock_perm),
            );
            endpoint_mut.rf_counter = endpoint_mut.rf_counter + 1;
            endpoint_mut.owning_threads = Ghost(
                endpoint_mut.owning_threads.view().insert((thread_ptr, 0)),
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
                thread_endpoint_no_change_imply_memory_management_inv(
                    *old(kernel),
                    *kernel,
                );
            };
            assert(kernel.process_management_inv()) by {
                assert(thread_endpoint_reference_added(
                    old(kernel).thread_map,
                    kernel.thread_map,
                    thread_ptr,
                    endpoint_ptr,
                    0,
                )) by {
                    thread_endpoint_reference_added_from_single_update(
                        old(kernel).thread_map,
                        kernel.thread_map,
                        thread_ptr,
                        endpoint_ptr,
                        0,
                    );
                };
                assert(endpoint_reference_added(
                    old(kernel).endpoint_map,
                    kernel.endpoint_map,
                    thread_ptr,
                    endpoint_ptr,
                    0,
                )) by {
                    endpoint_reference_added_from_single_update(
                        old(kernel).endpoint_map,
                        kernel.endpoint_map,
                        thread_ptr,
                        endpoint_ptr,
                        0,
                    );
                };
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
                    kernel.thread_map,
                    kernel.endpoint_map,
                )) by {
                    thread_endpoint_queue_wf_preserved_for_queue_fields(
                        old(kernel).thread_map,
                        kernel.thread_map,
                        old(kernel).endpoint_map,
                        kernel.endpoint_map,
                    );
                };
                assert(container_thread_endpoint_wf(
                    kernel.container_map,
                    kernel.thread_map,
                    kernel.endpoint_map,
                )) by {
                    reveal(container_thread_endpoint_wf);
                    reveal(thread_endpoint_reference_added);
                    reveal(thread_endpoint_ref_counter_wf);
                    reveal(container_endpoint_wf);
                };
                assert(container_thread_scheduler_wf(kernel.container_map, kernel.thread_map, kernel.scheduler_map)) by {
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
            assert({
                &&& lock_id_aligned(kernel, &*lctx)
                &&& kernel.endpoint_map.lock_id_by_key(endpoint_ptr)
                    == old(kernel).endpoint_map.lock_id_by_key(endpoint_ptr)
                &&& kernel.thread_map.lock_id_by_key(thread_ptr)
                    == old(kernel).thread_map.lock_id_by_key(thread_ptr)
            }) by {
                reveal(lock_id_aligned);
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
                lock_id_fields_eq_imply_eq();
            };
            assert(thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![current_thread_ptr, thread_ptr],
            )) by {
                thread_endpoint_reference_added_from_single_update(
                    old(kernel).thread_map, kernel.thread_map, thread_ptr, endpoint_ptr, 0);
                reveal(thread_endpoint_reference_added);
            };
            assert(endpoint_objects_unlocked_except(
                kernel.endpoint_map, lctx.thread_id(), set![endpoint_ptr],
            )) by {
                endpoint_reference_added_from_single_update(
                    old(kernel).endpoint_map, kernel.endpoint_map,
                    thread_ptr, endpoint_ptr, 0);
                reveal(endpoint_reference_added);
            };
        }
        kernel.wunlock_thread(
            thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm),
        );
        kernel.wunlock_endpoint(
            endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm),
        );
        proof {
            assert({
                &&& kernel.thread_map.spec_index(current_thread_ptr)
                    == old(kernel).thread_map.spec_index(current_thread_ptr)
                &&& kernel.thread_map.lock_id_by_key(current_thread_ptr)
                    == old(kernel).thread_map.lock_id_by_key(current_thread_ptr)
            }) by {
                reveal(thread_perms_wf);
                lock_id_fields_eq_imply_eq();
            };
        }
    }


}
