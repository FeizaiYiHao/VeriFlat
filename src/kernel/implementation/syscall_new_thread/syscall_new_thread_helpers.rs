use vstd::prelude::*;
use vstd::assert_seqs_equal;
use vstd::assert_sets_equal;
use crate::*;
verus! {

    // TODO(proof-design): The 4K/2M/1G conservation bridges in
    // container_process_allocator_quota_wf_preserved_on_thread_add remain
    // until the fold producers expose the corresponding post-state facts.


        /// Commit path: allocate 4k page, create thread, release all locks.
        pub(super) fn add_new_thread_to_proc_container_and_scheduler(
            kernel: &mut KernelK,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            process_ptr: RwLockProcessPtr,
            current_thread_ptr: RwLockThreadPtr,
            container_ptr: RwLockContainerPtr,
            scheduler_ptr: RwLockSchedulerPtr,
            process_lock_perm: Tracked<LockPerm>,
            current_thread_lock_perm: Tracked<LockPerm>,
            cpu_lock_perm: Tracked<LockPerm>,
            scheduler_lock_perm: Tracked<LockPerm>,
        )
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(kernel).inv(),
                lctx.kernel_view_locking_state() is Acquire,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
                old(kernel).scheduler_map.dom().contains(scheduler_ptr),
                old(kernel).process_map.dom().contains(process_ptr),
                old(kernel).thread_map.dom().contains(current_thread_ptr),
                old(kernel).container_map.dom().contains(container_ptr),
                lctx.lock_id_set() =~= set![
                    (old(kernel).cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id)),
                    (old(kernel).scheduler_map.lock_id_by_key(scheduler_ptr),
                        KernelObjId::Scheduler(scheduler_ptr)),
                    (old(kernel).process_map.lock_id_by_key(process_ptr),
                        KernelObjId::Process(process_ptr)),
                    (old(kernel).thread_map.lock_id_by_key(current_thread_ptr),
                        KernelObjId::Thread(current_thread_ptr)),
                ],
                cpu_lock_perm.view().state() is WriteLock,
                cpu_lock_perm.view().thread_id() == lctx.thread_id(),
                cpu_lock_perm.view().lock_id() == old(kernel).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(kernel).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(kernel).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                scheduler_lock_perm.view().state() is WriteLock,
                scheduler_lock_perm.view().thread_id() == lctx.thread_id(),
                scheduler_lock_perm.view().lock_id() == old(kernel).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                scheduler_lock_perm.view().ordering_lock_id().major
                    == SCHEDULER_LOCK_MAJOR,
                old(kernel).scheduler_map.spec_index(scheduler_ptr).wlocked_by(&lctx),
                old(kernel).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                old(kernel).container_map.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
                process_lock_perm.view().state() is WriteLock,
                process_lock_perm.view().thread_id() == lctx.thread_id(),
                process_lock_perm.view().lock_id() == old(kernel).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                process_lock_perm.view().ordering_lock_id().major
                    == PROCESS_LOCK_MAJOR,
                old(kernel).process_map.spec_index(process_ptr).wlocked_by(&lctx),
                old(kernel).process_map.spec_index(process_ptr).being_killed() == false,
                old(kernel).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                current_thread_lock_perm.view().state() is WriteLock,
                current_thread_lock_perm.view().thread_id() == lctx.thread_id(),
                current_thread_lock_perm.view().lock_id()
                    == old(kernel).thread_map.spec_index(current_thread_ptr)
                        .locking_thread()->Write_lock_id,
                current_thread_lock_perm.view().ordering_lock_id().major
                    == THREAD_LOCK_MAJOR,
                old(kernel).thread_map.spec_index(current_thread_ptr).wlocked_by(&lctx),
                old(kernel).thread_map.spec_index(current_thread_ptr).being_killed() == false,
                old(kernel).thread_map.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
                old(kernel).thread_map.spec_index(current_thread_ptr).view().owning_container == container_ptr,
                old(kernel).thread_map.spec_index(current_thread_ptr).view().temp_alloc_clean(),
                old(kernel).thread_map.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
                old(kernel).thread_map.spec_index(current_thread_ptr).view().quota_4k >= 1,
                old(kernel).thread_map.lock_id_by_key(current_thread_ptr).major == THREAD_LOCK_MAJOR,
                kernel_objects_unlocked_except(
                    old(kernel), old(lctx).thread_id(), Some(cpu_id),
                    Some(scheduler_ptr), Some(process_ptr),
                    Some(current_thread_ptr), None),
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
                final(kernel).all_objects_unlocked(final(lctx)),
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(kernel)),
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
                // Full U-change.
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

            proof {
                assert({
                    &&& kernel.cpu_array.lock_id_by_index(cpu_id).major
                        == CPU_LOCK_MAJOR_RUNNING
                    &&& kernel.scheduler_map.lock_id_by_key(scheduler_ptr).major
                        == SCHEDULER_LOCK_MAJOR
                    &&& kernel.process_map.lock_id_by_key(process_ptr).major
                        == PROCESS_LOCK_MAJOR
                }) by {
                    reveal(cpu_array_wf);
                    reveal(scheduler_perms_wf);
                    reveal(process_perms_wf);
                };
                assert(lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)) by {
                    let cpu_lock = (
                        kernel.cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id),
                    );
                    let scheduler_lock = (
                        kernel.scheduler_map.lock_id_by_key(scheduler_ptr),
                        KernelObjId::Scheduler(scheduler_ptr),
                    );
                    let process_lock = (
                        kernel.process_map.lock_id_by_key(process_ptr),
                        KernelObjId::Process(process_ptr),
                    );
                    let thread_lock = (
                        kernel.thread_map.lock_id_by_key(current_thread_ptr),
                        KernelObjId::Thread(current_thread_ptr),
                    );
                    let held_set = set![
                        cpu_lock,
                        scheduler_lock,
                        process_lock,
                        thread_lock,
                    ];
                    if !lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR) {
                        let held = choose|held: HeldLock|
                            #![trigger lctx.lock_id_set().contains(held)]
                            lctx.lock_id_set().contains(held)
                            && !(held.0.major < ALLOCATOR_CACHE_MAJOR);
                        vstd::set::axiom_set_ext_equal(lctx.lock_id_set(), held_set);
                        if held != thread_lock {
                            vstd::set::lemma_set_insert_different(
                                set![cpu_lock, scheduler_lock, process_lock],
                                held,
                                thread_lock,
                            );
                        }
                        if held != process_lock {
                            vstd::set::lemma_set_insert_different(
                                set![cpu_lock, scheduler_lock], held, process_lock);
                        }
                        if held != scheduler_lock {
                            vstd::set::lemma_set_insert_different(
                                set![cpu_lock], held, scheduler_lock);
                        }
                        if held != cpu_lock {
                            vstd::set::lemma_set_insert_different(
                                Set::<HeldLock>::empty(), held, cpu_lock);
                            vstd::set::lemma_set_empty(held);
                        }
                    }
                };
            }

            let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(kernel,
                current_thread_ptr, container_ptr, cpu_id,
                Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm),
            );
            let page_index = page_ptr2page_index(page_ptr);

            proof {
                assert(page_ptr != current_thread_ptr) by {
                    reveal(thread_pages_wf);
                };
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
            }
            let (new_thread_ptr, Tracked(new_thread_lock_perm)) = create_thread_from_staged_page_merged(kernel,
                page_ptr, process_ptr, current_thread_ptr, container_ptr, scheduler_ptr,
                Tracked(&mut *lctx), Tracked(&page_lock_perm),
                Tracked(&process_lock_perm), Tracked(&current_thread_lock_perm),
                Tracked(&scheduler_lock_perm),
            );

            proof {
                assert(kernel.thread_map.lock_id_by_key(new_thread_ptr)
                    != kernel.thread_map.lock_id_by_key(current_thread_ptr)) by {
                    reveal(thread_perms_wf);
                    reveal(thread_cpu_wf);
                };
            }
            kernel.wunlock_thread(new_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm));
            kernel.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
            kernel.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
            kernel.wunlock_thread(
                current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm),
            );
            kernel.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
            kernel.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

            proof {
                steps.end_kernel_step(&*kernel, &*lctx);
            }
        }

        /// Retype a staged page, wire the new thread into its owners, and
        /// re-establish the kernel invariants.
        #[verifier::spinoff_prover]
        pub(crate) fn create_thread_from_staged_page_merged(
            kernel: &mut KernelK,
            page_ptr: PagePtr,
            process_ptr: RwLockProcessPtr,
            staging_thread_ptr: RwLockThreadPtr,
            container_ptr: RwLockContainerPtr,
            scheduler_ptr: RwLockSchedulerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(page_lock_perm): Tracked<&LockPerm>,
            Tracked(process_lock_perm): Tracked<&LockPerm>,
            Tracked(staging_thread_lock_perm): Tracked<&LockPerm>,
            Tracked(scheduler_lock_perm): Tracked<&LockPerm>,
        ) -> (ret: (RwLockThreadPtr, Tracked<LockPerm>))
            requires
                old(kernel).inv(),
                page_ptr_valid(page_ptr),
                old(kernel).process_map.dom().contains(process_ptr),
                old(kernel).process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                old(kernel).thread_map.dom().contains(staging_thread_ptr),
                old(kernel).thread_map.spec_index(staging_thread_ptr).view().owning_proc == process_ptr,
                old(kernel).thread_map.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
                old(kernel).container_map.dom().contains(container_ptr),
                old(kernel).container_map.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
                old(kernel).process_map.spec_index(process_ptr).being_killed() == false,
                old(kernel).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == old(lctx).thread_id(),
                process_lock_perm.lock_id() == old(kernel).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(kernel).scheduler_map.dom().contains(scheduler_ptr),
                old(kernel).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                old(kernel).scheduler_map.spec_index(scheduler_ptr).wlocked_by(old(lctx)),
                scheduler_lock_perm.state() is WriteLock,
                scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
                scheduler_lock_perm.lock_id() == old(kernel).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                old(kernel).thread_map.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view()
                    =~= Set::<PagePtr>::empty().insert(page_ptr),
                old(kernel).thread_map.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
                old(kernel).thread_map.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
                old(kernel).thread_map.spec_index(staging_thread_ptr).view().quota_4k >= 1,
                old(kernel).thread_map.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
                old(kernel).thread_map.spec_index(staging_thread_ptr).wlocked_by(old(lctx)),
                staging_thread_lock_perm.state() is WriteLock,
                staging_thread_lock_perm.thread_id() == old(lctx).thread_id(),
                staging_thread_lock_perm.lock_id()
                    == old(kernel).thread_map.spec_index(staging_thread_ptr)
                        .locking_thread()->Write_lock_id,
                old(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
                old(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == (PageState::Owned4k{ thread_ptr: staging_thread_ptr }),
                page_lock_perm.state() is WriteLock,
                page_lock_perm.thread_id() == old(lctx).thread_id(),
                page_lock_perm.lock_id() == old(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
                old(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view()
                    .wlocked_by(old(lctx)),
                old(lctx).kernel_view_locking_state() is Release,
                lock_id_aligned(old(kernel), old(lctx)),
            ensures
                final(kernel).inv(),
                ret.0 == page_ptr,
                ret.1.view().state() is WriteLock,
                ret.1.view().thread_id() == final(lctx).thread_id(),
                ret.1.view().lock_id() == final(kernel).thread_map.spec_index(page_ptr).locking_thread()->Write_lock_id,
                final(kernel).thread_map.spec_index(page_ptr).is_init(),
                final(kernel).thread_map.spec_index(page_ptr).wlocked_by(final(lctx)),
                final(kernel).thread_map.dom()
                    =~= old(kernel).thread_map.dom().insert(page_ptr),
                final(kernel).thread_map.spec_index(page_ptr).view().free_quota_pending_clean(),
                final(kernel).thread_map.spec_index(page_ptr).view().temp_alloc_clean(),
                final(kernel).thread_map.spec_index(page_ptr).view().state is SCHEDULED,
                final(kernel).thread_map.spec_index(page_ptr).view().owning_container == container_ptr,
                final(kernel).thread_map.spec_index(page_ptr).view()
                    .endpoint_descriptors.spec_index(0) is None,
                final(kernel).thread_map.spec_index(page_ptr).view().endpoint_descriptors.wf(),
                final(kernel).thread_map.spec_index(page_ptr).being_killed() == false,
                final(kernel).process_map.dom().contains(process_ptr),
                final(kernel).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
                final(kernel).process_map.spec_index(process_ptr).being_killed() == false,
                final(kernel).thread_map.spec_index(staging_thread_ptr).view().temp_alloc_clean(),
                final(kernel).thread_map.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
                final(kernel).thread_map.dom().contains(staging_thread_ptr),
                final(kernel).thread_map.spec_index(staging_thread_ptr).being_killed()
                    == old(kernel).thread_map.spec_index(staging_thread_ptr)
                        .being_killed(),
                final(kernel).thread_map.spec_index(staging_thread_ptr).wlocked_by(final(lctx)),
                staging_thread_lock_perm.lock_id()
                    == final(kernel).thread_map.spec_index(staging_thread_ptr)
                        .locking_thread()->Write_lock_id,
                final(kernel).thread_map.lock_id_by_key(staging_thread_ptr)
                    == old(kernel).thread_map.lock_id_by_key(staging_thread_ptr),
                kernel_u_new_thread_changed(
                    kernel_k_to_kernel_u(*old(kernel)),
                    kernel_k_to_kernel_u(*final(kernel)),
                    process_ptr,
                ),
                process_lock_perm.lock_id() == final(kernel).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                final(kernel).process_map.lock_id_by_key(process_ptr)
                    == old(kernel).process_map.lock_id_by_key(process_ptr),
                final(kernel).scheduler_map.dom().contains(scheduler_ptr),
                final(kernel).scheduler_map.spec_index(scheduler_ptr).wlocked_by(final(lctx)),
                final(kernel).scheduler_map.spec_index(scheduler_ptr).being_killed() == false,
                scheduler_lock_perm.lock_id() == final(kernel).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                final(kernel).scheduler_map.lock_id_by_key(scheduler_ptr)
                    == old(kernel).scheduler_map.lock_id_by_key(scheduler_ptr),
                final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
                final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view()
                    .wlocked_by(final(lctx)),
                page_lock_perm.lock_id() == final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
                lock_id_aligned(final(kernel), final(lctx)),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state()
                    == old(lctx).kernel_view_locking_state(),
                final(kernel).pagetable_map == old(kernel).pagetable_map,
                final(kernel).iommu_table_map == old(kernel).iommu_table_map,
                final(kernel).endpoint_map == old(kernel).endpoint_map,
                final(kernel).pcid_allocator_map == old(kernel).pcid_allocator_map,
                final(kernel).allocator_4k_map == old(kernel).allocator_4k_map,
                final(kernel).allocator_2m_map == old(kernel).allocator_2m_map,
                final(kernel).allocator_1g_map == old(kernel).allocator_1g_map,
                final(kernel).container_map.dom() == old(kernel).container_map.dom(),
                forall|c: RwLockContainerPtr|
                    #![trigger final(kernel).container_map.spec_index(c).locking_thread()]
                    old(kernel).container_map.dom().contains(c)
                    ==> final(kernel).container_map.spec_index(c).locking_thread()
                        == old(kernel).container_map.spec_index(c).locking_thread(),
                forall|c_ptr: RwLockContainerPtr|
                    #![trigger final(kernel).container_map.spec_index(c_ptr).view().subtree_set]
                    old(kernel).container_map.dom().contains(c_ptr) ==>
                        final(kernel).container_map.spec_index(c_ptr).view().subtree_set
                            == old(kernel).container_map.spec_index(c_ptr).view().subtree_set,
                final(kernel).cpu_array == old(kernel).cpu_array,
                final(lctx).lock_id_set() ==
                    old(lctx).lock_id_set()
                        .remove((old(kernel).page_array.lock_id_by_index(
                            page_ptr2page_index(page_ptr)),
                            KernelObjId::Page(page_ptr2page_index(page_ptr))))
                        .insert((final(kernel).page_array.lock_id_by_index(
                            page_ptr2page_index(page_ptr)),
                            KernelObjId::Page(page_ptr2page_index(page_ptr))))
                        .insert((final(kernel).thread_map.lock_id_by_key(page_ptr),
                            KernelObjId::Thread(page_ptr))),
                scheduler_objects_unlocked_except(
                    old(kernel).scheduler_map,
                    old(lctx).thread_id(),
                    set![scheduler_ptr],
                ) ==> scheduler_objects_unlocked_except(
                    final(kernel).scheduler_map,
                    final(lctx).thread_id(),
                    set![scheduler_ptr],
                ),
                process_objects_unlocked_except(
                    old(kernel).process_map,
                    old(lctx).thread_id(),
                    set![process_ptr],
                ) ==> process_objects_unlocked_except(
                    final(kernel).process_map,
                    final(lctx).thread_id(),
                    set![process_ptr],
                ),
                page_objects_unlocked_except(
                    old(kernel).page_array,
                    old(lctx).thread_id(),
                    set![page_ptr2page_index(page_ptr)],
                ) ==> page_objects_unlocked_except(
                    final(kernel).page_array,
                    final(lctx).thread_id(),
                    set![page_ptr2page_index(page_ptr)],
                ),
                thread_objects_unlocked_except(
                    old(kernel).thread_map,
                    old(lctx).thread_id(),
                    set![staging_thread_ptr],
                ) ==> thread_objects_unlocked_except(
                    final(kernel).thread_map,
                    final(lctx).thread_id(),
                    set![staging_thread_ptr, page_ptr],
                ),
        {
            proof {
                assert(
                    kernel.process_map.view().spec_index(process_ptr).is_init()
                    && kernel.process_map.view().spec_index(process_ptr).addr()
                        == process_ptr
                    && kernel.process_map.spec_index(process_ptr).is_init()
                ) by {
                    reveal(process_perms_wf);
                };
                assert(
                    kernel.container_map.dom().contains(container_ptr)
                    && kernel.container_map.view().spec_index(container_ptr).is_init()
                    && kernel.container_map.view().spec_index(container_ptr).addr()
                        == container_ptr
                ) by {
                    reveal(container_perms_wf);
                    reveal(container_process_wf);
                };
                assert(container_tree_fields_wf(kernel.container_map)) by {
                    reveal(container_perms_wf);
                };
                assert(
                    kernel.scheduler_map.view().spec_index(scheduler_ptr).is_init()
                    && kernel.scheduler_map.view().spec_index(scheduler_ptr).addr()
                        == scheduler_ptr
                    && kernel.scheduler_map.spec_index(scheduler_ptr).is_init()
                ) by {
                    reveal(scheduler_perms_wf);
                };
                assert(
                    kernel.thread_map.spec_index(staging_thread_ptr).is_init()
                    && !kernel.thread_map.dom().contains(page_ptr)
                ) by {
                    reveal(thread_perms_wf);
                    reveal(thread_pages_wf);
                };
                assert(
                    kernel.container_map.spec_index(
                        container_ptr
                    ).view().uppertree_seq.view().no_duplicates()
                    && !kernel.container_map.spec_index(container_ptr)
                        .view().uppertree_seq.view().to_set()
                        .contains(container_ptr)
                ) by {
                    kernel.container_map.spec_index(container_ptr)
                        .view().uppertree_seq.view().to_set_ensures();
                    reveal(container_uppertree_seq_wf);

                    reveal(container_tree_fields_wf);
                };
                assert(
                    kernel.process_map.spec_index(
                        process_ptr
                    ).view().owned_threads.view().len() < usize::MAX
                ) by {
                    let threads = kernel.process_map.spec_index(
                        process_ptr
                    ).view().owned_threads.view();
                    assert(threads.no_duplicates()) by {
                        reveal(process_perms_wf);
                        reveal(LinkedList::wf_value_list);
                        reveal(LinkedList::value_list_unique);
                    };
                    reveal(process_thread_wf);
                    lemma_thread_ptr_seq_len_bounded(&*kernel, threads);
                };
                assert(
                    kernel.scheduler_map.spec_index(
                        scheduler_ptr
                    ).view().queue.view().len() < usize::MAX
                ) by {
                    let threads = kernel.scheduler_map.spec_index(
                        scheduler_ptr
                    ).view().queue.view();
                    assert(threads.no_duplicates()) by {
                        reveal(scheduler_perms_wf);
                        reveal(LinkedList::wf_value_list);
                        reveal(LinkedList::value_list_unique);
                    };
                    reveal(container_thread_scheduler_wf);
                    lemma_thread_ptr_seq_len_bounded(&*kernel, threads);
                };
                let page_index = page_ptr2page_index(page_ptr);
                assert(index_valid(NUM_PAGES, page_index)) by {
                    page_ptr_valid_imply_page_index_valid();
                };
                assert(
                    kernel.page_array.spec_index(page_index).view().is_init()
                    && kernel.page_array.spec_index(page_index).view().view().inv()
                    && kernel.page_array.spec_index(
                        page_index
                    ).view().view().perm_4k.view().is_some()
                    && kernel.page_array.spec_index(
                        page_index
                    ).view().view().addr == page_ptr
                ) by {
                    reveal(page_array_wf);
                };
            }

            // ---- Inlined retype: create thread, flip page state, insert into thread_map ----
            let container_rodata = kernel.container_map.borrow_rodata(container_ptr);
            let container_ro = container_rodata.borrow();
            let container_depth = container_ro.depth;

            let process_rodata = kernel.process_map.borrow_rodata(process_ptr);
            let process_ro = process_rodata.borrow();
            let process_depth = process_ro.depth;
            let proc_pagetable = process_ro.pagetable;

            let thread_value = Thread::new_fresh(
                container_ptr,
                container_depth,
                process_ptr,
                process_depth,
                proc_pagetable,
                Ghost(kernel.container_map.spec_index(container_ptr).view().uppertree_seq.view()),
            );

            let page_index = page_ptr2page_index(page_ptr);
            assert(lctx.lock_entry_contains(
                old(kernel).page_array.lock_id_by_index(page_index),
                KernelObjId::Page(page_index),
            )) by {
                reveal(lock_id_aligned);
            };
            let ghost old_page_lock_id = kernel.page_array.lock_id_by_index(page_index);
            proof {
                assert(kernel.page_array.inv()) by {
                    reveal(page_array_wf);
                };
            }
            let page_mut = kernel.page_array.borrow_mut(page_index, Tracked(&*lctx), Tracked(page_lock_perm));
            let Tracked(page_perm) = take_perm_4k(page_mut);
            page_mut.state = PageState::Allocated4k{ state: Allocated4KPageState::AsThread };
            proof {
                lctx.update_lock_id(
                    KernelObjId::Page(page_index),
                    old_page_lock_id,
                    kernel.page_array.lock_id_by_index(page_index),
                );
                assert(lock_id_aligned(kernel, &*lctx)) by {
                    reveal(lock_id_aligned);
                };
            }

            let (Tracked(thread_rwlock_perm), Tracked(thread_perm)) = retype_page_perm_to_thread(
                page_ptr, thread_value, Tracked(page_perm),
                Tracked(&mut *lctx), Ghost(KernelObjId::Thread(page_ptr)),
            );

            kernel.thread_map.insert_with_perm(
                page_ptr,
                Tracked(thread_rwlock_perm),
                (),
                Ghost(()),
                Ghost(()),
            );
            let ghost fresh_thread_lock_id =
                kernel.thread_map.lock_id_by_key(page_ptr);
            proof {
                lctx.enter_kernel_view_release();
            }

            proof {
                assert(
                    kernel.thread_map.view().dom().contains(staging_thread_ptr)
                ) by {
                    vstd::set::axiom_set_ext_equal(
                        kernel.thread_map.dom(),
                        old(kernel).thread_map.dom().insert(page_ptr),
                    );
                };
                assert(
                    kernel.thread_map.view().spec_index(staging_thread_ptr).is_init()
                ) by {
                    reveal(thread_perms_wf);
                    reveal(LockedMap::perms_wf);
                };
                assert(
                    kernel.thread_map.view().spec_index(staging_thread_ptr).addr()
                        == staging_thread_ptr
                ) by {
                    reveal(thread_perms_wf);
                    reveal(LockedMap::perms_wf);
                };
            }
            {
                let staging_thread_mut = kernel.thread_map.borrow_mut(
                    staging_thread_ptr,
                    Tracked(&*lctx),
                    Tracked(staging_thread_lock_perm),
                );
                staging_thread_mut.temp_alloc_cache_4k = Ghost(
                    staging_thread_mut.temp_alloc_cache_4k.view().remove(page_ptr),
                );
                staging_thread_mut.quota_4k = staging_thread_mut.quota_4k - 1;
            }
            // ---- End inlined retype ----

            proof {
                assert(kernel.container_map.perms_wf()) by {
                    reveal(container_perms_wf);
                };
                let uppers = old(kernel).container_map
                    .spec_index(container_ptr).view().uppertree_seq.view();
                assert(uppers.to_set().subset_of(
                    kernel.container_map.dom(),
                )) by {
                    uppers.to_set_ensures();
                    reveal(container_uppertree_seq_wf);
                };
                add_thread_to_container_sets(
                    &mut kernel.container_map, container_ptr, page_ptr,
                    uppers,
                );
            }

            proof {
                assert(old(kernel).process_map.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr) == false) by {
                    reveal(process_thread_wf);
                    if old(kernel).process_map.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr) {
                        assert(old(kernel).thread_map.spec_index(page_ptr).view().owning_proc == process_ptr) by {
                            reveal(process_thread_wf);
                        };
                    }
                }
            }
            proof {
                assert(
                    kernel.thread_map.view().spec_index(page_ptr).is_init()
                    && kernel.thread_map.view().spec_index(page_ptr).addr() == page_ptr
                ) by {
                    reveal(thread_perms_wf);
                    reveal(LockedMap::perms_wf);
                };
            }
            let thread_mut = kernel.thread_map.borrow_mut(page_ptr, Tracked(&*lctx), Tracked(&thread_perm));
            let (node_addr, mut node_perm) = thread_mut.proc_linkedlist_node.take();
            node_update_value(node_addr, &mut node_perm, page_ptr);
            let process_mut = kernel.process_map.borrow_mut(process_ptr, Tracked(&*lctx), Tracked(process_lock_perm));
            proof {
                assert(
                    process_mut.owned_threads.wf()
                    && process_mut.owned_threads.length != usize::MAX
                ) by {
                    reveal(process_perms_wf);
                    reveal(LinkedList::wf_value_list);
                };
            }
            process_mut.owned_threads.push_tail(node_addr, node_perm);

            let (sched_node_addr, mut sched_node_perm) = thread_mut.scheduler_linkedlist_node.take();
            node_update_value(sched_node_addr, &mut sched_node_perm, page_ptr);
            let scheduler_mut = kernel.scheduler_map.borrow_mut(scheduler_ptr, Tracked(&*lctx), Tracked(scheduler_lock_perm));
            proof {
                assert(
                    scheduler_mut.queue.wf()
                    && scheduler_mut.queue.length != usize::MAX
                ) by {
                    reveal(scheduler_perms_wf);
                    reveal(LinkedList::wf_value_list);
                };
                assert(!scheduler_mut.queue.view().contains(page_ptr)) by {
                    reveal(container_thread_scheduler_wf);
                };
            }
            scheduler_mut.queue.push_tail(sched_node_addr, sched_node_perm);
            thread_mut.state = ThreadState::SCHEDULED;

            proof {
                lctx.update_lock_id(
                    KernelObjId::Thread(page_ptr),
                    fresh_thread_lock_id,
                    kernel.thread_map.lock_id_by_key(page_ptr),
                );
                assert(kernel.subsystems_inv()) by {
                    reveal(KernelK::default_pagetable_wf);
                    reveal(cpu_array_wf);
                    reveal(container_perms_wf);
                    reveal(container_tree_fields_wf);
                    reveal(process_perms_wf);
                    reveal(thread_temp_alloc_empty_unless_wlocked);
                    reveal(allocator_perms_wf);
                    reveal(thread_perms_wf);

                    reveal(thread_free_quota_pending_empty_unless_wlocked);
                    reveal(page_array_wf);
                    reveal(scheduler_perms_wf);
                };
                assert(kernel.memory_management_inv()) by {
                    assert(allocator_pages_wf(kernel.page_array, kernel.allocator_4k_map, kernel.allocator_2m_map, kernel.allocator_1g_map)) by {
                        allocator_4k_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_4k_map, kernel.allocator_4k_map);
                        allocator_2m_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_2m_map, kernel.allocator_2m_map);
                        allocator_1g_pages_wf_preserved_for_page_state_eq(old(kernel).page_array, kernel.page_array, old(kernel).allocator_1g_map, kernel.allocator_1g_map);
                    };
                    assert(container_page_owner_wf(
                        kernel.container_map,
                        kernel.page_array,
                    )) by {
                        container_page_owner_wf_preserved_for_owning_container_eq(
                            old(kernel).container_map,
                            kernel.container_map,
                            old(kernel).page_array,
                            kernel.page_array,
                        );
                    };
                    assert(container_process_page_pagetable_wf(kernel.container_map, kernel.process_map, kernel.pagetable_map, kernel.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(page_pagetable_wf(kernel.pagetable_map, kernel.page_array)) by {
                        page_pagetable_wf_preserved_for_nonmapped_page_change(
                            old(kernel).pagetable_map,
                            kernel.pagetable_map,
                            old(kernel).page_array,
                            kernel.page_array,
                            page_index,
                        );
                    };
                    assert(iommu_table_pages_wf(kernel.iommu_table_map, kernel.page_array)) by {
                        iommu_table_pages_wf_preserved_for_non_iommu_page_change(
                            kernel.iommu_table_map,
                            old(kernel).page_array,
                            kernel.page_array,
                            page_ptr,
                        );
                    };
                    assert(pcid_allocator_pages_wf(kernel.page_array, kernel.pcid_allocator_map)) by {
                        pcid_allocator_pages_wf_preserved_for_page_state_eq(
                            old(kernel).page_array, kernel.page_array,
                            old(kernel).pcid_allocator_map, kernel.pcid_allocator_map);
                    };
                    assert(container_pages_wf(
                        kernel.page_array,
                        kernel.container_map,
                    )) by {
                        container_pages_wf_preserved_for_page_state_eq(
                            old(kernel).page_array,
                            kernel.page_array,
                            old(kernel).container_map,
                            kernel.container_map,
                        );
                    };
                    assert(process_pages_wf(
                        kernel.page_array,
                        kernel.process_map,
                    )) by {
                        process_pages_wf_preserved_for_page_state_eq(
                            old(kernel).page_array,
                            kernel.page_array,
                            old(kernel).process_map,
                            kernel.process_map,
                        );
                    };
                    assert(container_process_allocator_quota_wf(kernel.container_map, kernel.process_map, kernel.thread_map, kernel.allocator_4k_map, kernel.allocator_2m_map, kernel.allocator_1g_map)) by {
                        reveal(container_uppertree_seq_wf);
                        container_process_allocator_quota_wf_preserved_on_thread_add(*old(kernel), *kernel, container_ptr, page_ptr, old(kernel).container_map.spec_index(container_ptr).view().uppertree_seq.view());
                    };
                    assert(container_allocator_wf(
                        kernel.container_map,
                        kernel.allocator_4k_map,
                        kernel.allocator_2m_map,
                        kernel.allocator_1g_map,
                    )) by {
                        reveal(container_allocator_wf);
                    };
                    assert(kernel.allocator_free_pages_wf()) by {
                        reveal(allocator_free_page_ptrs_wf);
                    };
                    assert(process_pagetable_match(kernel.process_map, kernel.pagetable_map)) by {
                        process_pagetable_match_preserved_for_process_reference_fields(
                            old(kernel).process_map,
                            kernel.process_map,
                            kernel.pagetable_map,
                        );
                    };
                    assert(process_iommu_table_match(
                        kernel.process_map,
                        kernel.iommu_table_map,
                    )) by {
                        process_iommu_table_match_preserved_for_process_reference_fields(
                            old(kernel).process_map, kernel.process_map,
                            kernel.iommu_table_map);
                    };
                    assert(hugepage_2m_wf(kernel.page_array)) by {
                        hugepage_2m_wf_preserved_for_page_state_eq(
                            old(kernel).page_array,
                            kernel.page_array,
                        );
                    };
                    assert(hugepage_1g_wf(kernel.page_array)) by {
                        hugepage_1g_wf_preserved_for_page_state_eq(
                            old(kernel).page_array,
                            kernel.page_array,
                        );
                    };
                    assert(pagetable_pages_wf(kernel.pagetable_map, kernel.page_array)) by {
                        reveal(pagetable_pages_wf);
                    };
                    assert(thread_pages_wf(kernel.thread_map, kernel.page_array)) by {
                        reveal(thread_perms_wf);
                        reveal(thread_pages_wf);
                    };
                    assert(thread_staged_pages_4k_wf(
                        kernel.thread_map, kernel.page_array,
                    )) by {
                        reveal(thread_staged_pages_4k_wf);
                    };
                    assert(thread_staged_pages_2m_wf(
                        kernel.thread_map, kernel.page_array,
                    )) by {
                        reveal(thread_staged_pages_2m_wf);
                    };
                    assert(thread_staged_pages_1g_wf(
                        kernel.thread_map, kernel.page_array,
                    )) by {
                        reveal(thread_staged_pages_1g_wf);
                    };
                    assert(endpoint_pages_wf(
                        kernel.endpoint_map,
                        kernel.page_array,
                    )) by {
                        endpoint_pages_wf_preserved_for_page_state_eq(
                            old(kernel).endpoint_map,
                            kernel.endpoint_map,
                            old(kernel).page_array,
                            kernel.page_array,
                        );
                    };
                    assert(container_allocator_free_4k_page_wf(kernel.allocator_4k_map, kernel.page_array)) by {
                        container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(
                            kernel.allocator_4k_map,
                            old(kernel).page_array,
                            kernel.page_array,
                            page_index,
                        );
                    };
                    assert(container_allocator_free_2m_page_wf(kernel.allocator_2m_map, kernel.page_array)) by {
                        container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(
                            kernel.allocator_2m_map,
                            old(kernel).page_array,
                            kernel.page_array,
                            page_index,
                        );
                    };
                    assert(container_allocator_free_1g_page_wf(kernel.allocator_1g_map, kernel.page_array)) by {
                        container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(
                            kernel.allocator_1g_map,
                            old(kernel).page_array,
                            kernel.page_array,
                            page_index,
                        );
                    };
                };
                assert(kernel.process_management_inv()) by {
                    assert(container_tree_wf(kernel.root_container, kernel.container_map)) by {
                        container_no_change_to_tree_fields_imply_wf(kernel.root_container, old(kernel).container_map, kernel.container_map);
                    };
                    assert(container_process_wf(kernel.container_map, kernel.process_map)) by {
                        assert(container_process_wf(
                            kernel.container_map,
                            old(kernel).process_map,
                        )) by {
                            reveal(container_process_wf);
                        };
                        container_process_wf_preserved_for_process_reference_fields(
                            kernel.container_map, old(kernel).process_map,
                            kernel.process_map);
                    };
                    assert(per_container_process_tree_wf(kernel.container_map, kernel.process_map)) by {
                        reveal(per_container_process_tree_wf); reveal(container_process_wf);
                        per_container_process_tree_wf_preserved_for_tree_fields_eq(kernel.container_map, old(kernel).process_map, kernel.process_map);
                    };
                    assert(container_endpoint_wf(kernel.container_map, kernel.endpoint_map)) by {
                        reveal(container_endpoint_wf);
                    };
                    assert(container_cpu_wf(kernel.container_map, kernel.cpu_array)) by {
                        reveal(container_cpu_wf);
                    };
                    assert(container_scheduler_wf(kernel.container_map, kernel.scheduler_map)) by {
                        reveal(container_scheduler_wf);
                    };
                    assert(container_pcid_allocator_wf(
                        kernel.container_map, kernel.pcid_allocator_map,
                    )) by {
                        assert(container_pcid_allocator_fields_unchanged(
                            old(kernel).container_map,
                            kernel.container_map,
                        )) by {
                            vstd::set::axiom_set_ext_equal(
                                old(kernel).container_map.dom(),
                                kernel.container_map.dom(),
                            );
                        };
                        container_pcid_allocator_wf_preserved_for_fields_unchanged(
                            old(kernel).container_map, kernel.container_map,
                            kernel.pcid_allocator_map);
                    };
                    assert(process_cpu_wf(kernel.process_map, kernel.cpu_array)) by {
                        reveal(process_cpu_wf);
                    };
                    assert(process_pcid_allocator_wf(
                        kernel.container_map, kernel.process_map, kernel.pcid_allocator_map,
                    )) by {
                        reveal(process_pcid_allocator_wf);
                    };
                    assert(thread_endpoint_ref_counter_wf(kernel.thread_map, kernel.endpoint_map)) by {
                        reveal(thread_endpoint_ref_counter_wf);
                    };
                    assert(thread_endpoint_queue_wf(kernel.thread_map, kernel.endpoint_map)) by {
                        reveal(thread_perms_wf);
                        reveal(thread_endpoint_queue_wf);
                    };
                    assert(thread_caller_callee_wf(kernel.thread_map)) by {
                        reveal(thread_caller_callee_wf);
                    };
                    assert(container_thread_endpoint_wf(
                        kernel.container_map,
                        kernel.thread_map,
                        kernel.endpoint_map,
                    )) by {
                        reveal(container_endpoint_wf);
                        reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf);
                        reveal(container_thread_endpoint_wf);
                    };
                    assert(container_thread_wf(kernel.container_map, kernel.thread_map)) by {
                        old(kernel).container_map.spec_index(container_ptr)
                            .view().uppertree_seq.view().to_set_ensures();
                        reveal(container_thread_wf);
                    };
                    assert(container_thread_scheduler_wf(kernel.container_map, kernel.thread_map, kernel.scheduler_map)) by {
                        reveal(container_thread_scheduler_wf);
                        reveal(container_thread_wf);
                        reveal(container_scheduler_wf);
                        assert(
                            old(kernel).scheduler_map.spec_index(scheduler_ptr).view().queue.wf()
                        ) by {
                            reveal(scheduler_perms_wf);
                        };
                        seq_push_lemma::<RwLockThreadPtr>();
                    };
                    assert(thread_cpu_wf(kernel.thread_map, kernel.cpu_array)) by {
                        reveal(thread_cpu_wf);
                    };
                    assert(kernel.thread_map.spec_index(page_ptr).view().container_depth
                        == kernel.process_map.spec_index(process_ptr)
                            .view_rodata().view().container_depth) by {
                        reveal(container_process_wf);
                    };
                    assert(kernel.thread_map.spec_index(page_ptr).view().proc_pagetable_ptr
                        == kernel.process_map.spec_index(process_ptr).view().pagetable) by {
                        reveal(process_pagetable_match);
                    };
                    assert(process_thread_wf(kernel.process_map, kernel.thread_map)) by {
                        assert(
                            old(kernel).process_map.spec_index(process_ptr).view().owned_threads.wf()
                        ) by {
                            reveal(process_perms_wf);
                        };
                        seq_push_lemma::<RwLockThreadPtr>();
                        reveal(process_thread_wf);
                    };
                };
                assert_seqs_equal!(
                    kernel_k_to_kernel_u(*kernel).process_map
                        .spec_index(process_ptr).owned_threads.subrange(
                            0,
                            kernel_k_to_kernel_u(*old(kernel)).process_map
                                .spec_index(process_ptr).owned_threads.len() as int,
                        )
                    == kernel_k_to_kernel_u(*old(kernel)).process_map
                        .spec_index(process_ptr).owned_threads,
                    i => {
                        seq_subrange_split_lemma::<RwLockThreadPtr>();
                    }
                );
                assert(kernel.thread_map.lock_id_by_key(staging_thread_ptr)
                    == old(kernel).thread_map.lock_id_by_key(staging_thread_ptr)) by {
                    reveal(thread_perms_wf);
                };
                assert(kernel.process_map.lock_id_by_key(process_ptr)
                    == old(kernel).process_map.lock_id_by_key(process_ptr)) by {
                    reveal(process_perms_wf);
                };
                assert(kernel.scheduler_map.lock_id_by_key(scheduler_ptr)
                    == old(kernel).scheduler_map.lock_id_by_key(scheduler_ptr)) by {
                    reveal(scheduler_perms_wf);
                };
                assert(lock_id_aligned(&*kernel, &*lctx)) by {
                    reveal(process_perms_wf);
                    reveal(scheduler_perms_wf);
                    reveal(thread_perms_wf);
                    reveal(lock_id_aligned);
                };
                assert(cpu_dirty_map_wf(
                    kernel.container_map,
                    kernel.process_map,
                    kernel.cpu_array,
                    kernel.cpu_tlb,
                    kernel.pagetable_map,
                )) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(
                    kernel.cpu_tlb,
                    kernel.pagetable_map,
                    kernel.cpu_array,
                )) by {
                    reveal(tlb_wf_spec);
                };
                assert(kernel.inv()) by {
                    assert(iommu_root_table_process_wf(
                        &kernel.iommu_root_table,
                        kernel.process_map,
                        kernel.iommu_table_map,
                    )) by {
                        iommu_root_table_process_wf_preserved_for_process_reference_fields(
                            &kernel.iommu_root_table, old(kernel).process_map,
                            kernel.process_map, kernel.iommu_table_map);
                    };
                    assert(process_pci_function_ownership_wf(
                        &kernel.iommu_root_table,
                        kernel.process_map,
                    )) by {
                        process_pci_function_ownership_wf_preserved_for_process_reference_fields(
                            &kernel.iommu_root_table, old(kernel).process_map,
                            kernel.process_map);
                    };
                    assert(iommu_tlb_wf_spec(
                        kernel.iommu_tlb,
                        &kernel.iommu_root_table,
                        kernel.process_map,
                        kernel.iommu_table_map,
                    )) by {
                        iommu_tlb_wf_spec_preserved_for_process_reference_fields(
                            kernel.iommu_tlb, &kernel.iommu_root_table,
                            old(kernel).process_map, kernel.process_map,
                            kernel.iommu_table_map);
                    };
                };
                assert(!old(lctx).lock_id_set()
                    .remove((old_page_lock_id, KernelObjId::Page(page_index)))
                    .insert((kernel.page_array.lock_id_by_index(page_index),
                        KernelObjId::Page(page_index)))
                    .contains((fresh_thread_lock_id,
                        KernelObjId::Thread(page_ptr)))) by {
                    reveal(lock_id_aligned);
                    vstd::set::lemma_set_remove_different(
                        old(lctx).lock_id_set(),
                        (fresh_thread_lock_id, KernelObjId::Thread(page_ptr)),
                        (old_page_lock_id, KernelObjId::Page(page_index)),
                    );
                    vstd::set::lemma_set_insert_different(
                        old(lctx).lock_id_set().remove((
                            old_page_lock_id, KernelObjId::Page(page_index))),
                        (fresh_thread_lock_id, KernelObjId::Thread(page_ptr)),
                        (kernel.page_array.lock_id_by_index(page_index),
                            KernelObjId::Page(page_index)),
                    );
                };
                assert(old(lctx).lock_id_set()
                    .remove((old_page_lock_id, KernelObjId::Page(page_index)))
                    .insert((kernel.page_array.lock_id_by_index(page_index),
                        KernelObjId::Page(page_index)))
                    .insert((fresh_thread_lock_id,
                        KernelObjId::Thread(page_ptr)))
                    .remove((fresh_thread_lock_id,
                        KernelObjId::Thread(page_ptr)))
                    == old(lctx).lock_id_set()
                        .remove((old_page_lock_id, KernelObjId::Page(page_index)))
                        .insert((kernel.page_array.lock_id_by_index(page_index),
                            KernelObjId::Page(page_index)))) by {
                    set_insert_remove_absent_lemma(
                        old(lctx).lock_id_set()
                            .remove((old_page_lock_id, KernelObjId::Page(page_index)))
                            .insert((kernel.page_array.lock_id_by_index(page_index),
                                KernelObjId::Page(page_index))),
                        (fresh_thread_lock_id, KernelObjId::Thread(page_ptr)),
                    );
                };
            }
            (page_ptr, Tracked(thread_perm))
        }


    /// Predicate: post_cm = pre_cm with t_ptr added to dc + ancestors' ghost sets.
    pub open spec fn container_map_gained_thread(
        pre_cm: ContainerLockedMap,
        post_cm: ContainerLockedMap,
        dc: RwLockContainerPtr,
        t_ptr: RwLockThreadPtr,
        uppers: Seq<RwLockContainerPtr>,
    ) -> bool {
        &&& post_cm.dom() == pre_cm.dom()
        // Direct container: owned_threads gained t_ptr; everything else of dc's view unchanged.
        &&& post_cm.spec_index(dc).view_user_ghost().owned_threads.view()
            =~= pre_cm.spec_index(dc).view_user_ghost().owned_threads.view().insert(t_ptr)
        // Every container OTHER than dc keeps its owned_threads (user-ghost).
        &&& forall|c: RwLockContainerPtr|
            #![trigger post_cm.spec_index(c).view_user_ghost().owned_threads]
            pre_cm.dom().contains(c) && c != dc
            ==>
            post_cm.spec_index(c).view_user_ghost().owned_threads
                == pre_cm.spec_index(c).view_user_ghost().owned_threads
        // Ancestor containers: each gained t_ptr in owned_indirect_threads.
        &&& forall|c: RwLockContainerPtr|
            #![trigger post_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            uppers.to_set().contains(c)
            ==>
            post_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads.view()
                =~= pre_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads.view().insert(t_ptr)
        // Every container NOT an ancestor keeps its owned_indirect_threads (kernel-ghost).
        &&& forall|c: RwLockContainerPtr|
            #![trigger post_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            pre_cm.dom().contains(c) && !uppers.to_set().contains(c)
            ==>
            post_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads
                == pre_cm.spec_index(c).view_kernel_ghost().owned_indirect_threads
    }

    /// Add t_ptr to dc's owned_threads + ancestors' owned_indirect_threads.
    pub proof fn add_thread_to_container_sets(
        tracked container_map: &mut ContainerLockedMap,
        dc: RwLockContainerPtr,
        t_ptr: RwLockThreadPtr,
        uppers: Seq<RwLockContainerPtr>,
    )
        requires
            old(container_map).perms_wf(),
            old(container_map).dom().contains(dc),
            uppers.to_set().subset_of(old(container_map).dom()),
            uppers.no_duplicates(),
            !uppers.to_set().contains(dc),
        ensures
            final(container_map).perms_wf(),
            final(container_map).dom() == old(container_map).dom(),
            container_map_gained_thread(*old(container_map), *final(container_map), dc, t_ptr, uppers),
            container_pcid_allocator_fields_unchanged(
                *old(container_map),
                *final(container_map),
            ),
            // Only the ghost sets moved: each container's payload + rodata + lock state is held.
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) ==>
                    final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view()
                    && final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata()
                    && final(container_map).spec_index(c).is_init() == old(container_map).spec_index(c).is_init()
                    && final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread()
                    && final(container_map).spec_index(c).being_killed() == old(container_map).spec_index(c).being_killed(),
    {
        container_map.update_user_ghost(dc, ContainerGhostU { owned_threads: Ghost(container_map.spec_index(dc).view_user_ghost().owned_threads.view().insert(t_ptr)) });
        add_thread_to_ancestor_sets(container_map, dc, t_ptr, uppers);
    }

    /// Recursive helper: insert t_ptr into ancestors' owned_indirect_threads.
    pub proof fn add_thread_to_ancestor_sets(
        tracked container_map: &mut ContainerLockedMap,
        dc: RwLockContainerPtr,
        t_ptr: RwLockThreadPtr,
        uppers: Seq<RwLockContainerPtr>,
    )
        requires
            old(container_map).perms_wf(),
            uppers.to_set().subset_of(old(container_map).dom()),
            uppers.no_duplicates(),
        ensures
            final(container_map).perms_wf(),
            final(container_map).dom() == old(container_map).dom(),
            // Each ancestor gained t_ptr in owned_indirect_threads.
            forall|c: RwLockContainerPtr| #![auto]
                uppers.to_set().contains(c) ==>
                    final(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads.view()
                        =~= old(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads.view().insert(t_ptr),
            // Every container NOT in uppers keeps its kernel-view ghost.
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) && !uppers.to_set().contains(c) ==>
                    final(container_map).spec_index(c).view_kernel_ghost() == old(container_map).spec_index(c).view_kernel_ghost(),
            // Only owned_indirect_threads (kernel-ghost) moves: every container's user-ghost is held.
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) ==>
                    final(container_map).spec_index(c).view_user_ghost() == old(container_map).spec_index(c).view_user_ghost(),
            // Ghost-only updates: every container's payload + rodata + lock state is held.
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) ==>
                    final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view()
                    && final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata()
                    && final(container_map).spec_index(c).is_init() == old(container_map).spec_index(c).is_init()
                    && final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread()
                    && final(container_map).spec_index(c).being_killed() == old(container_map).spec_index(c).being_killed(),
        decreases uppers.len(),
    {
        if uppers.len() > 0 {
            let c0 = uppers.spec_index(0);
            assert(uppers.to_set().contains(c0)) by {
                uppers.to_set_ensures();
            };
            container_map.update_kernel_ghost(c0, ContainerGhostK { owned_indirect_threads: Ghost(container_map.spec_index(c0).view_kernel_ghost().owned_indirect_threads.view().insert(t_ptr)) });
            assert(uppers.drop_first().to_set().subset_of(
                container_map.dom(),
            )) by {
                uppers.to_set_ensures();
                uppers.drop_first().to_set_ensures();
                broadcast use vstd::seq_lib::lemma_seq_subrange_elements;
            };
            add_thread_to_ancestor_sets(container_map, dc, t_ptr, uppers.drop_first());
            assert(!uppers.drop_first().to_set().contains(c0)) by {
                uppers.drop_first().to_set_ensures();
                if uppers.drop_first().contains(c0) {
                    let k = choose|k: int| 0 <= k < uppers.drop_first().len() && uppers.drop_first().spec_index(k) == c0;
                }
            };
            assert_sets_equal!(
                uppers.to_set()
                    == uppers.drop_first().to_set().insert(c0),
                c => {
                    uppers.to_set_ensures();
                    uppers.drop_first().to_set_ensures();
                    if uppers.contains(c) && c != c0 {
                        let i = choose|i: int|
                            0 <= i < uppers.len()
                                && uppers.spec_index(i) == c;
                        assert({
                            &&& i > 0
                            &&& uppers.drop_first().spec_index(i - 1) == c
                        }) by {
                            uppers.to_set_ensures();
                        };
                    }
                    if uppers.drop_first().contains(c) {
                        let i = choose|i: int|
                            0 <= i < uppers.drop_first().len()
                                && uppers.drop_first().spec_index(i) == c;
                        assert(uppers.spec_index(i + 1) == c) by {
                            uppers.drop_first().to_set_ensures();
                        };
                    }
                }
            );
        }
    }

    /// Conservation law preserved across creating one thread.
    pub proof fn container_process_allocator_quota_wf_preserved_on_thread_add(
        pre: KernelK,
        post: KernelK,
        dc: RwLockContainerPtr,
        t_ptr: RwLockThreadPtr,
        uppers: Seq<RwLockContainerPtr>,
    )
        requires
            container_process_allocator_quota_wf(
                pre.container_map, pre.process_map, pre.thread_map,
                pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map,
            ),
            container_process_wf(pre.container_map, pre.process_map),
            container_thread_wf(pre.container_map, pre.thread_map),
            pre.container_map.dom().contains(dc),
            container_map_gained_thread(pre.container_map, post.container_map, dc, t_ptr, uppers),
            forall|c: RwLockContainerPtr| #![auto]
                pre.container_map.dom().contains(c) ==>
                    post.container_map.spec_index(c).view() == pre.container_map.spec_index(c).view()
                    && post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata(),
            post.allocator_4k_map == pre.allocator_4k_map,
            post.allocator_2m_map == pre.allocator_2m_map,
            post.allocator_1g_map == pre.allocator_1g_map,
            post.process_map.dom() == pre.process_map.dom(),
            forall|p: RwLockProcessPtr|
                #![trigger post.process_map.spec_index(p).view()]
                post.process_map.dom().contains(p) ==>
                    process_effective_quota_4k(post.process_map.spec_index(p)) == process_effective_quota_4k(pre.process_map.spec_index(p))
                    && process_effective_quota_2m(post.process_map.spec_index(p)) == process_effective_quota_2m(pre.process_map.spec_index(p))
                    && process_effective_quota_1g(post.process_map.spec_index(p)) == process_effective_quota_1g(pre.process_map.spec_index(p)),
            post.thread_map.dom() =~= pre.thread_map.dom().insert(t_ptr),
            pre.thread_map.dom().contains(t_ptr) == false,
            forall|t: RwLockThreadPtr|
                #![trigger post.thread_map.spec_index(t).view()]
                pre.thread_map.dom().contains(t) ==>
                    thread_effective_quota_4k(post.thread_map.spec_index(t))
                        == thread_effective_quota_4k(pre.thread_map.spec_index(t))
                    && thread_effective_quota_2m(post.thread_map.spec_index(t))
                        == thread_effective_quota_2m(pre.thread_map.spec_index(t))
                    && thread_effective_quota_1g(post.thread_map.spec_index(t))
                        == thread_effective_quota_1g(pre.thread_map.spec_index(t))
                    && post.thread_map.spec_index(t).view().direct_free_quota_pending_4k
                        == pre.thread_map.spec_index(t).view().direct_free_quota_pending_4k
                    && post.thread_map.spec_index(t).view().direct_free_quota_pending_2m
                        == pre.thread_map.spec_index(t).view().direct_free_quota_pending_2m
                    && post.thread_map.spec_index(t).view().direct_free_quota_pending_1g
                        == pre.thread_map.spec_index(t).view().direct_free_quota_pending_1g
                    && post.thread_map.spec_index(t).view().indirect_free_quota_pending_4k
                        == pre.thread_map.spec_index(t).view().indirect_free_quota_pending_4k
                    && post.thread_map.spec_index(t).view().indirect_free_quota_pending_2m
                        == pre.thread_map.spec_index(t).view().indirect_free_quota_pending_2m
                    && post.thread_map.spec_index(t).view().indirect_free_quota_pending_1g
                        == pre.thread_map.spec_index(t).view().indirect_free_quota_pending_1g,
            thread_effective_quota_4k(post.thread_map.spec_index(t_ptr)) == 0,
            thread_effective_quota_2m(post.thread_map.spec_index(t_ptr)) == 0,
            thread_effective_quota_1g(post.thread_map.spec_index(t_ptr)) == 0,
            post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view() == 0,
            post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view() == 0,
            post.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view() == 0,
            forall|c: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c).view_rodata().view().depth]
                uppers.to_set().contains(c) ==>
                    post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(post.container_map.spec_index(c).view_rodata().view().depth as int) == 0
                    && post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(post.container_map.spec_index(c).view_rodata().view().depth as int) == 0
                    && post.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(post.container_map.spec_index(c).view_rodata().view().depth as int) == 0,
        ensures
            container_process_allocator_quota_wf(
                post.container_map, post.process_map, post.thread_map,
                post.allocator_4k_map, post.allocator_2m_map, post.allocator_1g_map,
            ),
    {
        assert(container_process_allocator_quota_wf(
            post.container_map, post.process_map, post.thread_map,
            post.allocator_4k_map, post.allocator_2m_map, post.allocator_1g_map,
        )) by {
            assert(
                container_process_allocator_quota_4k_wf(
                    pre.container_map, pre.process_map, pre.thread_map,
                    pre.allocator_4k_map,
                )
                && container_process_allocator_quota_2m_wf(
                    pre.container_map, pre.process_map, pre.thread_map,
                    pre.allocator_2m_map,
                )
                && container_process_allocator_quota_1g_wf(
                    pre.container_map, pre.process_map, pre.thread_map,
                    pre.allocator_1g_map,
                )
                && container_process_wf(pre.container_map, pre.process_map)
                && container_thread_wf(pre.container_map, pre.thread_map)
            ) by {
                reveal(container_process_allocator_quota_4k_wf);
                reveal(container_process_allocator_quota_2m_wf);
                reveal(container_process_allocator_quota_1g_wf);
                reveal(container_process_wf);
                reveal(container_thread_wf);
            };

            // 4k.
            assert forall|c_ptr: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
                post.container_map.dom().contains(c_ptr)
            implies
                post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(post.process_map.spec_index(p_ptr)))
                    + thread_effective_quota_4k_fold_sum(
                        post.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                        post.thread_map,
                    )
                    + thread_direct_pending_4k_fold_sum(
                        post.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                        post.thread_map,
                    )
                    + thread_indirect_pending_4k_fold_sum_at_depth(
                        post.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view(),
                        post.thread_map,
                        post.container_map.spec_index(c_ptr).view_rodata().view().depth as int,
                    )
                    + post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                    == post.allocator_4k_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
            by {
                reveal(container_process_allocator_quota_4k_wf);
                reveal(container_process_wf);
                reveal(container_thread_wf);
                let s_p = post.container_map.spec_index(c_ptr).view().owned_processes.view();
                let d = post.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                lemma_process_effective_quota_4k_fold_eq(s_p, pre.process_map, post.process_map);
                let s_d_pre = pre.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view();
                if c_ptr == dc {
                    lemma_thread_effective_quota_4k_fold_insert_zero(
                        s_d_pre, pre.thread_map, post.thread_map, t_ptr,
                    );
                    lemma_thread_direct_pending_4k_fold_insert_zero(s_d_pre, pre.thread_map, post.thread_map, t_ptr);
                } else {
                    lemma_thread_effective_quota_4k_fold_eq(
                        s_d_pre, pre.thread_map, post.thread_map,
                    );
                    lemma_thread_direct_pending_4k_fold_eq(s_d_pre, pre.thread_map, post.thread_map);
                }
                let s_i_pre = pre.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view();
                if uppers.to_set().contains(c_ptr) {
                    lemma_thread_indirect_pending_4k_fold_insert_zero_at_depth(s_i_pre, pre.thread_map, post.thread_map, t_ptr, d);
                } else {
                    lemma_thread_indirect_pending_4k_fold_eq_at_depth(s_i_pre, pre.thread_map, post.thread_map, d);
                }
            };

            // 2m.
            assert forall|c_ptr: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
                post.container_map.dom().contains(c_ptr)
            implies
                post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_2m(post.process_map.spec_index(p_ptr)))
                    + thread_effective_quota_2m_fold_sum(
                        post.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                        post.thread_map,
                    )
                    + post.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t: RwLockThreadPtr| sum + post.thread_map.spec_index(t).view().direct_free_quota_pending_2m.view())
                    + post.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t: RwLockThreadPtr| sum + post.thread_map.spec_index(t).view().indirect_free_quota_pending_2m.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
                    + post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
                    == post.allocator_2m_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
            by {
                reveal(container_process_allocator_quota_2m_wf);
                reveal(container_process_wf);
                reveal(container_thread_wf);
                let s_p = post.container_map.spec_index(c_ptr).view().owned_processes.view();
                let d = post.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                lemma_process_effective_quota_2m_fold_eq(s_p, pre.process_map, post.process_map);
                let s_d_pre = pre.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view();
                if c_ptr == dc {
                    lemma_thread_effective_quota_2m_fold_insert_zero(
                        s_d_pre, pre.thread_map, post.thread_map, t_ptr,
                    );
                    lemma_thread_direct_pending_2m_fold_insert_zero(s_d_pre, pre.thread_map, post.thread_map, t_ptr);
                } else {
                    lemma_thread_effective_quota_2m_fold_eq(
                        s_d_pre, pre.thread_map, post.thread_map,
                    );
                    lemma_thread_direct_pending_2m_fold_eq(s_d_pre, pre.thread_map, post.thread_map);
                }
                let s_i_pre = pre.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view();
                if uppers.to_set().contains(c_ptr) {
                    lemma_thread_indirect_pending_2m_fold_insert_zero_at_depth(s_i_pre, pre.thread_map, post.thread_map, t_ptr, d);
                } else {
                    lemma_thread_indirect_pending_2m_fold_eq_at_depth(s_i_pre, pre.thread_map, post.thread_map, d);
                }
            };

            // 1g.
            assert forall|c_ptr: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
                post.container_map.dom().contains(c_ptr)
            implies
                post.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| sum + process_effective_quota_1g(post.process_map.spec_index(p_ptr)))
                    + thread_effective_quota_1g_fold_sum(
                        post.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                        post.thread_map,
                    )
                    + post.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t: RwLockThreadPtr| sum + post.thread_map.spec_index(t).view().direct_free_quota_pending_1g.view())
                    + post.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t: RwLockThreadPtr| sum + post.thread_map.spec_index(t).view().indirect_free_quota_pending_1g.view().spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().depth as int))
                    + post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
                    == post.allocator_1g_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
            by {
                reveal(container_process_allocator_quota_1g_wf);
                reveal(container_process_wf);
                reveal(container_thread_wf);
                let s_p = post.container_map.spec_index(c_ptr).view().owned_processes.view();
                let d = post.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                lemma_process_effective_quota_1g_fold_eq(s_p, pre.process_map, post.process_map);
                let s_d_pre = pre.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view();
                if c_ptr == dc {
                    lemma_thread_effective_quota_1g_fold_insert_zero(
                        s_d_pre, pre.thread_map, post.thread_map, t_ptr,
                    );
                    lemma_thread_direct_pending_1g_fold_insert_zero(s_d_pre, pre.thread_map, post.thread_map, t_ptr);
                } else {
                    lemma_thread_effective_quota_1g_fold_eq(
                        s_d_pre, pre.thread_map, post.thread_map,
                    );
                    lemma_thread_direct_pending_1g_fold_eq(s_d_pre, pre.thread_map, post.thread_map);
                }
                let s_i_pre = pre.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view();
                if uppers.to_set().contains(c_ptr) {
                    lemma_thread_indirect_pending_1g_fold_insert_zero_at_depth(s_i_pre, pre.thread_map, post.thread_map, t_ptr, d);
                } else {
                    lemma_thread_indirect_pending_1g_fold_eq_at_depth(s_i_pre, pre.thread_map, post.thread_map, d);
                }
            };
            reveal(container_process_allocator_quota_4k_wf);
            reveal(container_process_allocator_quota_2m_wf);
            reveal(container_process_allocator_quota_1g_wf);
        };
    }

    /// User-view change predicate for successful new_thread.
    pub open spec fn kernel_u_new_thread_changed(
        old_u: KernelU,
        new_u: KernelU,
        process_ptr: RwLockProcessPtr,
    ) -> bool {
        &&& new_u.cpu_array == old_u.cpu_array
        &&& new_u.process_map.dom() == old_u.process_map.dom()
        &&& old_u.process_map.dom().contains(process_ptr)
        // Thread-local quota pays for the page; the process tier is unchanged.
        &&& new_u.process_map.spec_index(process_ptr).quota_4k
                == old_u.process_map.spec_index(process_ptr).quota_4k
        &&& new_u.process_map.spec_index(process_ptr).owned_threads.len()
                == old_u.process_map.spec_index(process_ptr).owned_threads.len() + 1
        &&& new_u.process_map.spec_index(process_ptr).owned_threads.subrange(
                0, old_u.process_map.spec_index(process_ptr).owned_threads.len() as int)
                == old_u.process_map.spec_index(process_ptr).owned_threads
        // Every other field of the targeted process preserved.
        &&& new_u.process_map.spec_index(process_ptr).pagetable      == old_u.process_map.spec_index(process_ptr).pagetable
        &&& new_u.process_map.spec_index(process_ptr).iommu_table    == old_u.process_map.spec_index(process_ptr).iommu_table
        &&& new_u.process_map.spec_index(process_ptr).quota_2m       == old_u.process_map.spec_index(process_ptr).quota_2m
        &&& new_u.process_map.spec_index(process_ptr).quota_1g       == old_u.process_map.spec_index(process_ptr).quota_1g
        &&& new_u.process_map.spec_index(process_ptr).parent         == old_u.process_map.spec_index(process_ptr).parent
        &&& new_u.process_map.spec_index(process_ptr).children       == old_u.process_map.spec_index(process_ptr).children
        &&& new_u.process_map.spec_index(process_ptr).depth          == old_u.process_map.spec_index(process_ptr).depth
        &&& new_u.process_map.spec_index(process_ptr).uppertree_seq  == old_u.process_map.spec_index(process_ptr).uppertree_seq
        &&& new_u.process_map.spec_index(process_ptr).subtree_set    == old_u.process_map.spec_index(process_ptr).subtree_set
        &&& new_u.process_map.spec_index(process_ptr).killed         == old_u.process_map.spec_index(process_ptr).killed
        // Every other process: projection unchanged.
        &&& forall|p: RwLockProcessPtr|
            #![trigger new_u.process_map.spec_index(p)]
            old_u.process_map.dom().contains(p) && p != process_ptr ==>
                new_u.process_map.spec_index(p) == old_u.process_map.spec_index(p)
    }
}
