use vstd::prelude::*;
use vstd::assert_seqs_equal;
use vstd::assert_sets_equal;
use crate::*;
verus! {

        /// Commit path: allocate 4k page, create thread, release all locks.
        pub(super) fn add_new_thread_to_proc_container_and_scheduler(
            krnl: &mut KernelK,
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
                old(krnl).inv(),
                lctx.kernel_view_locking_state() is Acquire,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
                old(krnl).sched_mp.dom().contains(scheduler_ptr),
                old(krnl).prc_mp.dom().contains(process_ptr),
                old(krnl).thr_mp.dom().contains(current_thread_ptr),
                old(krnl).ctn_mp.dom().contains(container_ptr),
                cpu_lock_perm.view().state() is WriteLock,
                cpu_lock_perm.view().thread_id() == lctx.thread_id(),
                cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().state == CpuState::Running,
                scheduler_lock_perm.view().state() is WriteLock,
                scheduler_lock_perm.view().thread_id() == lctx.thread_id(),
                scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                scheduler_lock_perm.view().ordering_lock_id().major == SCHEDULER_LOCK_MAJOR,
                old(krnl).sched_mp.spec_index(scheduler_ptr).wlocked_by(&lctx),
                old(krnl).sched_mp.spec_index(scheduler_ptr).being_killed() == false,
                old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
                process_lock_perm.view().state() is WriteLock,
                process_lock_perm.view().thread_id() == lctx.thread_id(),
                process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
                process_lock_perm.view().ordering_lock_id().major == PROCESS_LOCK_MAJOR,
                old(krnl).prc_mp.spec_index(process_ptr).wlocked_by(&lctx),
                old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
                old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                current_thread_lock_perm.view().state() is WriteLock,
                current_thread_lock_perm.view().thread_id() == lctx.thread_id(),
                current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
                current_thread_lock_perm.view().ordering_lock_id().major == THREAD_LOCK_MAJOR,
                old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(&lctx),
                old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1,
                old(krnl).thr_mp.lock_id_by_key(current_thread_ptr).major == THREAD_LOCK_MAJOR,
                kernel_objects_unlocked_except(old(krnl), old(lctx).thread_id(), Some(cpu_id), Some(scheduler_ptr), Some(process_ptr), Some(current_thread_ptr), None),
                old(lctx).page_lock_map().dom().is_empty(),
                old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
                old(lctx).container_lock_map().dom().is_empty(),
                old(lctx).process_lock_map().dom() =~= set![process_ptr],
                old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
                old(lctx).endpoint_lock_map().dom().is_empty(),
                old(lctx).scheduler_lock_map().dom() =~= set![scheduler_ptr],
                old(lctx).pcid_allocator_lock_map().dom().is_empty(),
                old(lctx).pagetable_lock_map().dom().is_empty(),
                old(lctx).iommu_table_lock_map().dom().is_empty(),
                old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
                old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
                old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
                old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(lctx).no_locks_held(),
                !final(krnl).cpu_arr.spec_index(cpu_id).view().locked_by_thread(final(lctx).thread_id()),
                !final(krnl).sched_mp.spec_index(scheduler_ptr).locked_by_thread(final(lctx).thread_id()),
                !final(krnl).prc_mp.spec_index(process_ptr).locked_by_thread(final(lctx).thread_id()),
                !final(krnl).thr_mp.spec_index(current_thread_ptr).locked_by_thread(final(lctx).thread_id()),
                final(krnl).all_objects_unlocked(final(lctx)),
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(krnl)),
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
                kernel_u_new_thread_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, process_ptr),
        {
            let tracked mut process_lock_perm = process_lock_perm.get();
            let tracked mut current_thread_lock_perm = current_thread_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            let tracked scheduler_lock_perm = scheduler_lock_perm.get();

            proof {
                assert({
                    &&& krnl.cpu_arr.lock_id_by_index(cpu_id).major == CPU_LOCK_MAJOR_RUNNING
                    &&& krnl.sched_mp.lock_id_by_key(scheduler_ptr).major == SCHEDULER_LOCK_MAJOR
                    &&& krnl.prc_mp.lock_id_by_key(process_ptr).major == PROCESS_LOCK_MAJOR
                }) by { reveal(cpu_array_wf); reveal(scheduler_perms_wf); reveal(process_perms_wf); };
            }

            let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, current_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm));
            let page_index = page_ptr2page_index(page_ptr);

            proof {
                assert(page_ptr != current_thread_ptr) by { reveal(thread_pages_wf); };
                assert({
                    &&& krnl.ctn_mp.dom().contains(container_ptr)
                    &&& krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr
                }) by { reveal(container_scheduler_wf); };
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            }
            let (new_thread_ptr, Tracked(new_thread_lock_perm)) = create_thread_from_staged_page_merged(krnl, page_ptr, process_ptr, current_thread_ptr, container_ptr, scheduler_ptr, Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(&process_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&scheduler_lock_perm));

            proof {
                assert(krnl.thr_mp.lock_id_by_key(new_thread_ptr) != krnl.thr_mp.lock_id_by_key(current_thread_ptr)) by { reveal(thread_perms_wf); reveal(thread_cpu_wf); };
            }
            krnl.wunlock_thread(new_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm));
            krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
            krnl.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
            krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
            krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

            proof {
                assert(lctx.no_locks_held()) by { reveal(LocalContext::no_locks_held); reveal(LocalContext::holds_no_allocator_locks); };
                steps.end_kernel_step(&*krnl, &*lctx);
            }
        }

        /// Retype a staged page, wire the new thread into its owners, and
        /// re-establish the krnl invariants.
        #[verifier::spinoff_prover]
        pub(crate) fn create_thread_from_staged_page_merged(
            krnl: &mut KernelK,
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
                old(krnl).inv(),
                page_ptr_valid(page_ptr),
                old(krnl).prc_mp.dom().contains(process_ptr),
                old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                old(krnl).thr_mp.dom().contains(staging_thread_ptr),
                old(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_proc == process_ptr,
                old(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
                old(krnl).ctn_mp.dom().contains(container_ptr),
                old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
                old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
                old(krnl).prc_mp.spec_index(process_ptr).wlocked_by(old(lctx)),
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == old(lctx).thread_id(),
                process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(krnl).sched_mp.dom().contains(scheduler_ptr),
                old(krnl).sched_mp.spec_index(scheduler_ptr).being_killed() == false,
                old(krnl).sched_mp.spec_index(scheduler_ptr).wlocked_by(old(lctx)),
                scheduler_lock_perm.state() is WriteLock,
                scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
                scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
                old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
                old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
                old(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 1,
                old(krnl).thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
                old(krnl).thr_mp.spec_index(staging_thread_ptr).wlocked_by(old(lctx)),
                staging_thread_lock_perm.state() is WriteLock,
                staging_thread_lock_perm.thread_id() == old(lctx).thread_id(),
                staging_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
                old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
                old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
                page_lock_perm.state() is WriteLock,
                page_lock_perm.thread_id() == old(lctx).thread_id(),
                page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
                old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(old(lctx)),
                old(lctx).kernel_view_locking_state() is Release,
                typed_lock_maps_aligned(old(krnl), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(krnl).inv(),
                ret.0 == page_ptr,
                ret.1.view().state() is WriteLock,
                ret.1.view().thread_id() == final(lctx).thread_id(),
                ret.1.view().lock_id() == final(krnl).thr_mp.spec_index(page_ptr).locking_thread()->Write_lock_id,
                final(krnl).thr_mp.spec_index(page_ptr).is_init(),
                final(krnl).thr_mp.spec_index(page_ptr).wlocked_by(final(lctx)),
                final(krnl).thr_mp.dom() =~= old(krnl).thr_mp.dom().insert(page_ptr),
                final(krnl).thr_mp.spec_index(page_ptr).view().free_quota_pending_clean(),
                final(krnl).thr_mp.spec_index(page_ptr).view().temp_alloc_clean(),
                final(krnl).thr_mp.spec_index(page_ptr).view().state is SCHEDULED,
                final(krnl).thr_mp.spec_index(page_ptr).view().owning_container == container_ptr,
                final(krnl).thr_mp.spec_index(page_ptr).view().endpoint_descriptors.spec_index(0) is None,
                final(krnl).thr_mp.spec_index(page_ptr).view().endpoint_descriptors.wf(),
                final(krnl).thr_mp.spec_index(page_ptr).being_killed() == false,
                final(krnl).prc_mp.dom().contains(process_ptr),
                final(krnl).prc_mp.spec_index(process_ptr).wlocked_by(final(lctx)),
                final(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
                final(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_clean(),
                final(krnl).thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
                final(krnl).thr_mp.dom().contains(staging_thread_ptr),
                final(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed(),
                final(krnl).thr_mp.spec_index(staging_thread_ptr).wlocked_by(final(lctx)),
                staging_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
                final(krnl).thr_mp.lock_id_by_key(staging_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(staging_thread_ptr),
                kernel_u_new_thread_changed(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), process_ptr),
                process_lock_perm.lock_id() == final(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
                final(krnl).prc_mp.lock_id_by_key(process_ptr) == old(krnl).prc_mp.lock_id_by_key(process_ptr),
                final(krnl).sched_mp.dom().contains(scheduler_ptr),
                final(krnl).sched_mp.spec_index(scheduler_ptr).wlocked_by(final(lctx)),
                final(krnl).sched_mp.spec_index(scheduler_ptr).being_killed() == false,
                scheduler_lock_perm.lock_id() == final(krnl).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                final(krnl).sched_mp.lock_id_by_key(scheduler_ptr) == old(krnl).sched_mp.lock_id_by_key(scheduler_ptr),
                final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
                final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(final(lctx)),
                page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
                final(lctx).page_lock_map() == old(lctx).page_lock_map().insert(page_ptr2page_index(page_ptr), TypedHeldLock {
                    lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write,
                }),
                final(lctx).thread_lock_map() == old(lctx).thread_lock_map().insert(page_ptr, TypedHeldLock {
                    lock_id: final(krnl).thr_mp.lock_id_by_key(page_ptr), mode: TypedLockMode::Write,
                }),
                final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
                final(lctx).container_lock_map() == old(lctx).container_lock_map(),
                final(lctx).process_lock_map() == old(lctx).process_lock_map(),
                final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
                final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
                final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
                final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
                final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
                final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
                final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                final(krnl).pt_mp == old(krnl).pt_mp,
                final(krnl).it_mp == old(krnl).it_mp,
                final(krnl).ep_mp == old(krnl).ep_mp,
                final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
                final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
                final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
                final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
                final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
                forall|c: RwLockContainerPtr|
                    #![trigger final(krnl).ctn_mp.spec_index(c).locking_thread()]
                    old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread(),
                forall|c_ptr: RwLockContainerPtr|
                    #![trigger final(krnl).ctn_mp.spec_index(c_ptr).view().subtree_set]
                    old(krnl).ctn_mp.dom().contains(c_ptr) ==> final(krnl).ctn_mp.spec_index(c_ptr).view().subtree_set == old(krnl).ctn_mp.spec_index(c_ptr).view().subtree_set,
                final(krnl).cpu_arr == old(krnl).cpu_arr,
                final(lctx).lock_id_set() == old(lctx).lock_id_set()
                    .remove((old(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr))))
                    .insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr))))
                    .insert((LockId {
                        container: LockOwnerId::NotApp,
                        process: LockOwnerId::NotApp,
                        major: THREAD_LOCK_MAJOR,
                        minor: page_ptr,
                    }, KernelObjId::Thread(page_ptr)))
                    .remove((LockId {
                        container: LockOwnerId::NotApp,
                        process: LockOwnerId::NotApp,
                        major: THREAD_LOCK_MAJOR,
                        minor: page_ptr,
                    }, KernelObjId::Thread(page_ptr)))
                    .insert((final(krnl).thr_mp.lock_id_by_key(page_ptr), KernelObjId::Thread(page_ptr))),
                scheduler_objects_unlocked_except(old(krnl).sched_mp, old(lctx).thread_id(), set![scheduler_ptr]) ==> scheduler_objects_unlocked_except(final(krnl).sched_mp, final(lctx).thread_id(), set![scheduler_ptr]),
                process_objects_unlocked_except(old(krnl).prc_mp, old(lctx).thread_id(), set![process_ptr]) ==> process_objects_unlocked_except(final(krnl).prc_mp, final(lctx).thread_id(), set![process_ptr]),
                page_objects_unlocked_except(old(krnl).pg_arr, old(lctx).thread_id(), set![page_ptr2page_index(page_ptr)]) ==> page_objects_unlocked_except(final(krnl).pg_arr, final(lctx).thread_id(), set![page_ptr2page_index(page_ptr)]),
                thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![staging_thread_ptr]) ==> thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![staging_thread_ptr, page_ptr]),
        {
            hide(new_thread_kernel_transition_framing);
            proof {
                assert(
                    krnl.prc_mp.view().spec_index(process_ptr).is_init()
                    && krnl.prc_mp.view().spec_index(process_ptr).addr() == process_ptr
                    && krnl.prc_mp.spec_index(process_ptr).is_init()
                ) by { reveal(process_perms_wf); };
                assert(
                    krnl.ctn_mp.dom().contains(container_ptr)
                    && krnl.ctn_mp.view().spec_index(container_ptr).is_init()
                    && krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr
                ) by { reveal(container_perms_wf); reveal(container_process_wf); };
                assert(
                    krnl.sched_mp.view().spec_index(scheduler_ptr).is_init()
                    && krnl.sched_mp.view().spec_index(scheduler_ptr).addr() == scheduler_ptr
                    && krnl.sched_mp.spec_index(scheduler_ptr).is_init()
                ) by { reveal(scheduler_perms_wf); };
                assert(krnl.thr_mp.spec_index(staging_thread_ptr).is_init() && !krnl.thr_mp.dom().contains(page_ptr)) by { reveal(thread_perms_wf); reveal(thread_pages_wf); };
                assert(
                    krnl.ctn_mp.spec_index(container_ptr).view().uppertree_seq.view().no_duplicates()
                    && !krnl.ctn_mp.spec_index(container_ptr).view().uppertree_seq.view().to_set().contains(container_ptr)
                ) by {
                    krnl.ctn_mp.spec_index(container_ptr).view().uppertree_seq.view().to_set_ensures();
                    reveal(container_perms_wf); reveal(container_uppertree_seq_wf); reveal(container_tree_fields_wf);
                };
                assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() < usize::MAX) by {
                    let threads = krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view();
                    assert(threads.no_duplicates()) by { reveal(process_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); };
                    reveal(process_thread_wf);
                    lemma_thread_ptr_seq_len_bounded(&*krnl, threads);
                };
                assert(krnl.sched_mp.spec_index(scheduler_ptr).view().queue.view().len() < usize::MAX) by {
                    let threads = krnl.sched_mp.spec_index(scheduler_ptr).view().queue.view();
                    assert(threads.no_duplicates()) by { reveal(scheduler_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); };
                    reveal(container_thread_scheduler_wf);
                    lemma_thread_ptr_seq_len_bounded(&*krnl, threads);
                };
                let page_index = page_ptr2page_index(page_ptr);
                assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
                assert(
                    krnl.pg_arr.inv()
                    &&
                    krnl.pg_arr.spec_index(page_index).view().is_init()
                    && krnl.pg_arr.spec_index(page_index).view().view().inv()
                    && krnl.pg_arr.spec_index(page_index).view().view().perm_4k.view().is_some()
                    && krnl.pg_arr.spec_index(page_index).view().view().addr == page_ptr
                ) by { reveal(page_array_wf); };
            }
            let container_rodata = krnl.ctn_mp.borrow_rodata(container_ptr);
            let container_ro = container_rodata.borrow();
            let container_depth = container_ro.depth;
            let process_rodata = krnl.prc_mp.borrow_rodata(process_ptr);
            let process_ro = process_rodata.borrow();
            let process_depth = process_ro.depth;
            let proc_pagetable = process_ro.pagetable;
            let thread_value = Thread::new_fresh(container_ptr, container_depth, process_ptr, process_depth, proc_pagetable, Ghost(krnl.ctn_mp.spec_index(container_ptr).view().uppertree_seq.view()));
            let page_index = page_ptr2page_index(page_ptr);
            let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
            let page_mut = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_lock_perm));
            let Tracked(page_perm) = take_perm_4k(page_mut);
            page_mut.state = PageState::Allocated4k { state: Allocated4KPageState::AsThread };
            proof {
                lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
                assert(krnl.thr_mp.perms_wf()) by { reveal(thread_perms_wf); };
            }
            let Tracked(thread_perm) = krnl.retype_page_to_thread_and_insert(page_ptr, thread_value, Tracked(page_perm), Tracked(&mut *lctx));
            let ghost fresh_thread_lock_id = krnl.thr_mp.lock_id_by_key(page_ptr);
            proof {
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            }
            proof {
                assert(krnl.thr_mp.view().dom().contains(staging_thread_ptr)) by { vstd::set::axiom_set_ext_equal(krnl.thr_mp.dom(), old(krnl).thr_mp.dom().insert(page_ptr)); };
                assert(krnl.thr_mp.view().spec_index(staging_thread_ptr).is_init() && krnl.thr_mp.view().spec_index(staging_thread_ptr).addr() == staging_thread_ptr) by { reveal(thread_perms_wf); reveal(LockedMap::perms_wf); };
            }
            let staging_thread_mut = krnl.thr_mp.borrow_mut_typed(staging_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(staging_thread_lock_perm));
            staging_thread_mut.temp_alloc_cache_4k = Ghost(staging_thread_mut.temp_alloc_cache_4k.view().remove(page_ptr));
            staging_thread_mut.quota_4k = staging_thread_mut.quota_4k - 1;
            proof {
                assert(old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr) == false) by {
                    reveal(process_thread_wf);
                    if old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr) {
                        assert(old(krnl).thr_mp.spec_index(page_ptr).view().owning_proc == process_ptr) by { reveal(process_thread_wf); };
                    }
                }
            }
            proof {
                assert(
                    krnl.thr_mp.view().spec_index(page_ptr).is_init()
                    && krnl.thr_mp.view().spec_index(page_ptr).addr() == page_ptr
                ) by { reveal(thread_perms_wf); reveal(LockedMap::perms_wf); };
                assert(!krnl.sched_mp.spec_index(scheduler_ptr).view().queue.view().contains(page_ptr)) by { reveal(container_thread_scheduler_wf); };
            }
            let thread_mut = krnl.thr_mp.borrow_mut_typed(page_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_perm));
            let ((node_addr, mut node_perm), (sched_node_addr, mut sched_node_perm)) = (thread_mut.proc_linkedlist_node.take(), thread_mut.scheduler_linkedlist_node.take());
            thread_mut.state = ThreadState::SCHEDULED;
            node_update_value(node_addr, &mut node_perm, page_ptr);
            proof { assert(krnl.prc_mp.perms_wf()) by { reveal(process_perms_wf); }; }
            let process_mut = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm));
            proof { assert(process_mut.owned_threads.wf() && process_mut.owned_threads.length != usize::MAX) by { reveal(process_perms_wf); reveal(LinkedList::wf_value_list); }; }
            process_mut.owned_threads.push_tail(node_addr, node_perm);
            node_update_value(sched_node_addr, &mut sched_node_perm, page_ptr);
            {
                proof { assert(krnl.sched_mp.perms_wf()) by { reveal(scheduler_perms_wf); }; }
                let scheduler_mut = krnl.sched_mp.borrow_mut_typed(scheduler_ptr, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(scheduler_lock_perm));
                proof { assert(scheduler_mut.queue.wf() && scheduler_mut.queue.length != usize::MAX) by { reveal(scheduler_perms_wf); reveal(LinkedList::wf_value_list); }; }
                scheduler_mut.queue.push_tail(sched_node_addr, sched_node_perm);
            }
            proof {
                assert(krnl.thr_mp.lock_id_by_key(staging_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(staging_thread_ptr)) by { reveal(thread_perms_wf); };
                assert(krnl.prc_mp.lock_id_by_key(process_ptr) == old(krnl).prc_mp.lock_id_by_key(process_ptr)) by { reveal(process_perms_wf); };
                assert(krnl.sched_mp.lock_id_by_key(scheduler_ptr) == old(krnl).sched_mp.lock_id_by_key(scheduler_ptr)) by { reveal(scheduler_perms_wf); };
                assert(krnl.ctn_mp.perms_wf()) by { reveal(container_perms_wf); };
                let uppers = old(krnl).ctn_mp.spec_index(container_ptr).view().uppertree_seq.view();
                assert(uppers.to_set().subset_of(krnl.ctn_mp.dom())) by {
                    uppers.to_set_ensures();
                    reveal(container_uppertree_seq_wf);
                };
                add_thread_to_container_sets(&mut krnl.ctn_mp, container_ptr, page_ptr, uppers);
                lctx.update_lock_id(KernelObjId::Thread(page_ptr), fresh_thread_lock_id, krnl.thr_mp.lock_id_by_key(page_ptr));
                assert(new_thread_kernel_transition_framing(*old(krnl), *krnl, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, page_ptr, proc_pagetable)) by {
                    reveal(new_thread_kernel_transition_framing);
                    reveal(container_perms_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(scheduler_perms_wf);
                    reveal(thread_free_quota_pending_empty_unless_wlocked);
                    seq_push_lemma::<RwLockThreadPtr>();
                };
                assert_seqs_equal!(
                    kernel_k_to_kernel_u(*krnl).process_map.spec_index(process_ptr).owned_threads.subrange(0, kernel_k_to_kernel_u(*old(krnl)).process_map.spec_index(process_ptr).owned_threads.len() as int)
                        == kernel_k_to_kernel_u(*old(krnl)).process_map.spec_index(process_ptr).owned_threads,
                    i => {
                        seq_subrange_split_lemma::<RwLockThreadPtr>();
                    }
                );
                assert(krnl.inv()) by { new_thread_close_kernel_inv(*old(krnl), *krnl, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, page_ptr, proc_pagetable); };
            }
            (page_ptr, Tracked(thread_perm))
        }

    pub open spec fn new_thread_kernel_transition_framing(
        pre: KernelK,
        post: KernelK,
        process_ptr: RwLockProcessPtr,
        staging_thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        scheduler_ptr: RwLockSchedulerPtr,
        page_ptr: PagePtr,
        proc_pagetable: RwLockPageTableRoot,
    ) -> bool {
        let page_index = page_ptr2page_index(page_ptr);
        let uppers = pre.ctn_mp.spec_index(container_ptr).view().uppertree_seq.view();
        &&& page_ptr_valid(page_ptr)
        &&& pre.prc_mp.dom().contains(process_ptr)
        &&& pre.thr_mp.dom().contains(staging_thread_ptr)
        &&& pre.ctn_mp.dom().contains(container_ptr)
        &&& pre.sched_mp.dom().contains(scheduler_ptr)
        &&& !pre.thr_mp.dom().contains(page_ptr)
        &&& pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr
        &&& pre.thr_mp.spec_index(staging_thread_ptr).view().owning_proc == process_ptr
        &&& pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr
        &&& pre.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr
        &&& pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == proc_pagetable
        &&& post.pt_mp == pre.pt_mp
        &&& post.it_mp == pre.it_mp
        &&& post.irt == pre.irt
        &&& post.cpu_arr == pre.cpu_arr
        &&& post.pcid_allc_mp == pre.pcid_allc_mp
        &&& post.ep_mp == pre.ep_mp
        &&& post.allc_4k_mp == pre.allc_4k_mp
        &&& post.allc_2m_mp == pre.allc_2m_mp
        &&& post.allc_1g_mp == pre.allc_1g_mp
        &&& post.cpu_tlb == pre.cpu_tlb
        &&& post.iommu_tlb == pre.iommu_tlb
        &&& post.rt_ctn == pre.rt_ctn
        &&& post.dflt_pt == pre.dflt_pt
        &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
        &&& pre.pg_arr.spec_index(page_index).view().view().state == PageState::Owned4k { thread_ptr: staging_thread_ptr }
        &&& post.pg_arr.spec_index(page_index).view().view().state == PageState::Allocated4k { state: Allocated4KPageState::AsThread }
        &&& post.pg_arr.spec_index(page_index).view().view().addr == pre.pg_arr.spec_index(page_index).view().view().addr
        &&& post.pg_arr.spec_index(page_index).view().view().owning_container == pre.pg_arr.spec_index(page_index).view().view().owning_container
        &&& forall|i: PageIndex|
            #![trigger index_valid(NUM_PAGES, i)]
            index_valid(NUM_PAGES, i) && (post.pg_arr.spec_index(i).view().view().state is Owned2m || pre.pg_arr.spec_index(i).view().view().state is Owned2m) ==>
                post.pg_arr.spec_index(i).view().view().state == pre.pg_arr.spec_index(i).view().view().state
        &&& forall|i: PageIndex|
            #![trigger index_valid(NUM_PAGES, i)]
            index_valid(NUM_PAGES, i) && (post.pg_arr.spec_index(i).view().view().state is Owned1g || pre.pg_arr.spec_index(i).view().view().state is Owned1g) ==>
                post.pg_arr.spec_index(i).view().view().state == pre.pg_arr.spec_index(i).view().view().state
        &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
        &&& forall|c: RwLockContainerPtr|
            #![trigger pre.ctn_mp.view().dom().contains(c)]
            #![trigger post.ctn_mp.view().dom().contains(c)]
            pre.ctn_mp.dom().contains(c) ==> {
                &&& post.ctn_mp.view().spec_index(c).is_init() == pre.ctn_mp.view().spec_index(c).is_init()
                &&& post.ctn_mp.view().spec_index(c).addr() == pre.ctn_mp.view().spec_index(c).addr()
            }
        &&& post.ctn_mp.spec_index(container_ptr).view_user_ghost().owned_threads.view() =~= pre.ctn_mp.spec_index(container_ptr).view_user_ghost().owned_threads.view().insert(page_ptr)
        &&& forall|c: RwLockContainerPtr|
            #![trigger pre.ctn_mp.spec_index(c).view_user_ghost().owned_threads]
            #![trigger post.ctn_mp.spec_index(c).view_user_ghost().owned_threads]
            pre.ctn_mp.dom().contains(c) && c != container_ptr ==>
                post.ctn_mp.spec_index(c).view_user_ghost().owned_threads == pre.ctn_mp.spec_index(c).view_user_ghost().owned_threads
        &&& forall|c: RwLockContainerPtr|
            #![trigger pre.ctn_mp.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            #![trigger post.ctn_mp.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            uppers.to_set().contains(c) ==>
                post.ctn_mp.spec_index(c).view_kernel_ghost().owned_indirect_threads.view() =~= pre.ctn_mp.spec_index(c).view_kernel_ghost().owned_indirect_threads.view().insert(page_ptr)
        &&& forall|c: RwLockContainerPtr|
            #![trigger pre.ctn_mp.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            #![trigger post.ctn_mp.spec_index(c).view_kernel_ghost().owned_indirect_threads]
            pre.ctn_mp.dom().contains(c) && !uppers.to_set().contains(c) ==>
                post.ctn_mp.spec_index(c).view_kernel_ghost().owned_indirect_threads == pre.ctn_mp.spec_index(c).view_kernel_ghost().owned_indirect_threads
        &&& forall|c: RwLockContainerPtr|
            #![trigger pre.ctn_mp.spec_index(c)]
            #![trigger post.ctn_mp.spec_index(c)]
            pre.ctn_mp.dom().contains(c) ==> {
                &&& post.ctn_mp.spec_index(c).view() == pre.ctn_mp.spec_index(c).view()
                &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
                &&& post.ctn_mp.spec_index(c).is_init() == pre.ctn_mp.spec_index(c).is_init()
                &&& post.ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
                &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
            }
        &&& post.prc_mp.dom() == pre.prc_mp.dom()
        &&& forall|p: RwLockProcessPtr|
            #![trigger pre.prc_mp.view().dom().contains(p)]
            #![trigger post.prc_mp.view().dom().contains(p)]
            pre.prc_mp.dom().contains(p) ==> {
                &&& post.prc_mp.view().spec_index(p).is_init() == pre.prc_mp.view().spec_index(p).is_init()
                &&& post.prc_mp.view().spec_index(p).addr() == pre.prc_mp.view().spec_index(p).addr()
            }
        &&& forall|p: RwLockProcessPtr|
            #![trigger pre.prc_mp.spec_index(p)]
            #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> {
                &&& post.prc_mp.spec_index(p).view_rodata() == pre.prc_mp.spec_index(p).view_rodata()
                &&& post.prc_mp.spec_index(p).view().pagetable == pre.prc_mp.spec_index(p).view().pagetable
                &&& post.prc_mp.spec_index(p).view().pcid == pre.prc_mp.spec_index(p).view().pcid
                &&& post.prc_mp.spec_index(p).view().iommu_table == pre.prc_mp.spec_index(p).view().iommu_table
                &&& post.prc_mp.spec_index(p).view().pci_function_ref_counter == pre.prc_mp.spec_index(p).view().pci_function_ref_counter
                &&& post.prc_mp.spec_index(p).view().owned_pci_functions == pre.prc_mp.spec_index(p).view().owned_pci_functions
            }
        &&& post.prc_mp.spec_index(process_ptr).view().owned_threads.view() == pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().push(page_ptr)
        &&& !pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr)
        &&& post.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr)
        &&& post.prc_mp.spec_index(process_ptr).view().owned_threads.map() == pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().insert(post.thr_mp.spec_index(page_ptr).view().proc_linkedlist_node.addr(), page_ptr)
        &&& post.prc_mp.spec_index(process_ptr).view().owned_threads.map().dom().contains(post.thr_mp.spec_index(page_ptr).view().proc_linkedlist_node.addr())
        &&& post.prc_mp.spec_index(process_ptr).view().owned_threads.map().spec_index(post.thr_mp.spec_index(page_ptr).view().proc_linkedlist_node.addr()) == page_ptr
        &&& forall|t: RwLockThreadPtr|
            #![trigger pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(t)]
            #![trigger post.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(t)]
            pre.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(t) ==>
                post.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(t)
        &&& forall|addr: usize|
            #![trigger pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().dom().contains(addr)]
            #![trigger post.prc_mp.spec_index(process_ptr).view().owned_threads.map().dom().contains(addr)]
            pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().dom().contains(addr) ==> {
                &&& post.prc_mp.spec_index(process_ptr).view().owned_threads.map().dom().contains(addr)
                &&& post.prc_mp.spec_index(process_ptr).view().owned_threads.map().spec_index(addr) == pre.prc_mp.spec_index(process_ptr).view().owned_threads.map().spec_index(addr)
            }
        &&& post.prc_mp.spec_index(process_ptr).view().quota_4k == pre.prc_mp.spec_index(process_ptr).view().quota_4k
        &&& post.prc_mp.spec_index(process_ptr).view().quota_2m == pre.prc_mp.spec_index(process_ptr).view().quota_2m
        &&& post.prc_mp.spec_index(process_ptr).view().quota_1g == pre.prc_mp.spec_index(process_ptr).view().quota_1g
        &&& post.prc_mp.spec_index(process_ptr).is_init() == pre.prc_mp.spec_index(process_ptr).is_init()
        &&& post.prc_mp.spec_index(process_ptr).view().parent_linkedlist_node == pre.prc_mp.spec_index(process_ptr).view().parent_linkedlist_node
        &&& post.prc_mp.spec_index(process_ptr).view().children == pre.prc_mp.spec_index(process_ptr).view().children
        &&& post.prc_mp.spec_index(process_ptr).view().uppertree_seq == pre.prc_mp.spec_index(process_ptr).view().uppertree_seq
        &&& post.prc_mp.spec_index(process_ptr).view().subtree_set == pre.prc_mp.spec_index(process_ptr).view().subtree_set
        &&& forall|p: RwLockProcessPtr|
            #![trigger pre.prc_mp.spec_index(p)]
            #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && p != process_ptr ==>
                post.prc_mp.spec_index(p) == pre.prc_mp.spec_index(p)
        &&& post.thr_mp.dom() =~= pre.thr_mp.dom().insert(page_ptr)
        &&& post.thr_mp.view().spec_index(page_ptr).is_init()
        &&& post.thr_mp.view().spec_index(page_ptr).addr() == page_ptr
        &&& forall|t: RwLockThreadPtr|
            #![trigger pre.thr_mp.view().dom().contains(t)]
            #![trigger post.thr_mp.view().dom().contains(t)]
            pre.thr_mp.dom().contains(t) ==> {
                &&& post.thr_mp.view().spec_index(t).is_init() == pre.thr_mp.view().spec_index(t).is_init()
                &&& post.thr_mp.view().spec_index(t).addr() == pre.thr_mp.view().spec_index(t).addr()
            }
        &&& forall|t: RwLockThreadPtr|
            #![trigger pre.thr_mp.spec_index(t)]
            #![trigger post.thr_mp.spec_index(t)]
            pre.thr_mp.dom().contains(t) && t != staging_thread_ptr ==>
                post.thr_mp.spec_index(t) == pre.thr_mp.spec_index(t)
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() == pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr)
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m == pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g == pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g
        &&& post.thr_mp.spec_index(staging_thread_ptr).is_init() == pre.thr_mp.spec_index(staging_thread_ptr).is_init()
        &&& forall|t: RwLockThreadPtr, staged_page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(staged_page_ptr)]
            #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(staged_page_ptr)]
            pre.thr_mp.dom().contains(t) ==>
                post.thr_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(staged_page_ptr) == pre.thr_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(staged_page_ptr)
        &&& forall|t: RwLockThreadPtr, staged_page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(staged_page_ptr)]
            #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(staged_page_ptr)]
            pre.thr_mp.dom().contains(t) ==>
                post.thr_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(staged_page_ptr) == pre.thr_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(staged_page_ptr)
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_clean()
        &&& post.thr_mp.spec_index(staging_thread_ptr).locking_thread() == pre.thr_mp.spec_index(staging_thread_ptr).locking_thread()
        &&& thread_effective_quota_4k(post.thr_mp.spec_index(staging_thread_ptr)) == thread_effective_quota_4k(pre.thr_mp.spec_index(staging_thread_ptr))
        &&& thread_effective_quota_2m(post.thr_mp.spec_index(staging_thread_ptr)) == thread_effective_quota_2m(pre.thr_mp.spec_index(staging_thread_ptr))
        &&& thread_effective_quota_1g(post.thr_mp.spec_index(staging_thread_ptr)) == thread_effective_quota_1g(pre.thr_mp.spec_index(staging_thread_ptr))
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_fields_equal(&pre.thr_mp.spec_index(staging_thread_ptr).view())
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().state == pre.thr_mp.spec_index(staging_thread_ptr).view().state
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().caller == pre.thr_mp.spec_index(staging_thread_ptr).view().caller
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().callee == pre.thr_mp.spec_index(staging_thread_ptr).view().callee
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().ipc_payload == pre.thr_mp.spec_index(staging_thread_ptr).view().ipc_payload
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().error_code == pre.thr_mp.spec_index(staging_thread_ptr).view().error_code
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().trap_frame == pre.thr_mp.spec_index(staging_thread_ptr).view().trap_frame
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().owning_container == pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().container_depth == pre.thr_mp.spec_index(staging_thread_ptr).view().container_depth
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().scheduler_linkedlist_node == pre.thr_mp.spec_index(staging_thread_ptr).view().scheduler_linkedlist_node
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().owning_proc == pre.thr_mp.spec_index(staging_thread_ptr).view().owning_proc
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().process_depth == pre.thr_mp.spec_index(staging_thread_ptr).view().process_depth
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().proc_pagetable_ptr == pre.thr_mp.spec_index(staging_thread_ptr).view().proc_pagetable_ptr
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().proc_linkedlist_node == pre.thr_mp.spec_index(staging_thread_ptr).view().proc_linkedlist_node
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors == pre.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors
        &&& forall|t: RwLockThreadPtr, edp_index: EndpointIdx|
            #![trigger pre.thr_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(edp_index as int)]
            #![trigger post.thr_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(edp_index as int)]
            pre.thr_mp.dom().contains(t) && edp_idx_valid(edp_index) ==>
                post.thr_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(edp_index as int) == pre.thr_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(edp_index as int)
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().blocking_endpoint_ptr == pre.thr_mp.spec_index(staging_thread_ptr).view().blocking_endpoint_ptr
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().blocking_endpoint_index == pre.thr_mp.spec_index(staging_thread_ptr).view().blocking_endpoint_index
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().endpoint_linkedlist_node == pre.thr_mp.spec_index(staging_thread_ptr).view().endpoint_linkedlist_node
        &&& post.thr_mp.spec_index(staging_thread_ptr).view().upper_container_seq == pre.thr_mp.spec_index(staging_thread_ptr).view().upper_container_seq
        &&& post.thr_mp.spec_index(page_ptr).view().state is SCHEDULED
        &&& post.thr_mp.spec_index(page_ptr).is_init()
        &&& post.thr_mp.spec_index(page_ptr).view().owning_container == container_ptr
        &&& post.thr_mp.spec_index(page_ptr).view().container_depth == pre.ctn_mp.spec_index(container_ptr).view_rodata().view().depth
        &&& post.thr_mp.spec_index(page_ptr).view().owning_proc == process_ptr
        &&& post.thr_mp.spec_index(page_ptr).view().process_depth == pre.prc_mp.spec_index(process_ptr).view_rodata().view().depth
        &&& post.thr_mp.spec_index(page_ptr).view().proc_pagetable_ptr == proc_pagetable
        &&& post.thr_mp.spec_index(page_ptr).view().upper_container_seq.view() == uppers
        &&& post.thr_mp.spec_index(page_ptr).view().caller is None
        &&& post.thr_mp.spec_index(page_ptr).view().callee is None
        &&& post.thr_mp.spec_index(page_ptr).view().blocking_endpoint_ptr is None
        &&& post.thr_mp.spec_index(page_ptr).view().blocking_endpoint_index is None
        &&& post.thr_mp.spec_index(page_ptr).view().free_quota_pending_clean()
        &&& post.thr_mp.spec_index(page_ptr).view().temp_alloc_clean()
        &&& post.thr_mp.spec_index(page_ptr).view().quota_4k == 0
        &&& post.thr_mp.spec_index(page_ptr).view().quota_2m == 0
        &&& post.thr_mp.spec_index(page_ptr).view().quota_1g == 0
        &&& forall|edp_index: EndpointIdx|
            #![trigger pre.thr_mp.spec_index(page_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int)]
            #![trigger post.thr_mp.spec_index(page_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int)]
            edp_idx_valid(edp_index) ==>
                post.thr_mp.spec_index(page_ptr).view().endpoint_descriptors.view().spec_index(edp_index as int) is None
        &&& post.sched_mp.dom() == pre.sched_mp.dom()
        &&& forall|s: RwLockSchedulerPtr|
            #![trigger pre.sched_mp.view().dom().contains(s)]
            #![trigger post.sched_mp.view().dom().contains(s)]
            pre.sched_mp.dom().contains(s) ==> {
                &&& post.sched_mp.view().spec_index(s).is_init() == pre.sched_mp.view().spec_index(s).is_init()
                &&& post.sched_mp.view().spec_index(s).addr() == pre.sched_mp.view().spec_index(s).addr()
            }
        &&& post.sched_mp.spec_index(scheduler_ptr).view().owning_container == pre.sched_mp.spec_index(scheduler_ptr).view().owning_container
        &&& post.sched_mp.spec_index(scheduler_ptr).is_init() == pre.sched_mp.spec_index(scheduler_ptr).is_init()
        &&& !pre.sched_mp.spec_index(scheduler_ptr).view().queue.view().contains(page_ptr)
        &&& post.sched_mp.spec_index(scheduler_ptr).view().queue.view() == pre.sched_mp.spec_index(scheduler_ptr).view().queue.view().push(page_ptr)
        &&& post.sched_mp.spec_index(scheduler_ptr).view().queue.view().contains(page_ptr)
        &&& post.sched_mp.spec_index(scheduler_ptr).view().queue.map() == pre.sched_mp.spec_index(scheduler_ptr).view().queue.map().insert(post.thr_mp.spec_index(page_ptr).view().scheduler_linkedlist_node.addr(), page_ptr)
        &&& post.sched_mp.spec_index(scheduler_ptr).view().queue.map().dom().contains(post.thr_mp.spec_index(page_ptr).view().scheduler_linkedlist_node.addr())
        &&& post.sched_mp.spec_index(scheduler_ptr).view().queue.map().spec_index(post.thr_mp.spec_index(page_ptr).view().scheduler_linkedlist_node.addr()) == page_ptr
        &&& forall|t: RwLockThreadPtr|
            #![trigger pre.sched_mp.spec_index(scheduler_ptr).view().queue.view().contains(t)]
            #![trigger post.sched_mp.spec_index(scheduler_ptr).view().queue.view().contains(t)]
            pre.sched_mp.spec_index(scheduler_ptr).view().queue.view().contains(t) ==>
                post.sched_mp.spec_index(scheduler_ptr).view().queue.view().contains(t)
        &&& forall|addr: usize|
            #![trigger pre.sched_mp.spec_index(scheduler_ptr).view().queue.map().dom().contains(addr)]
            #![trigger post.sched_mp.spec_index(scheduler_ptr).view().queue.map().dom().contains(addr)]
            pre.sched_mp.spec_index(scheduler_ptr).view().queue.map().dom().contains(addr) ==> {
                &&& post.sched_mp.spec_index(scheduler_ptr).view().queue.map().dom().contains(addr)
                &&& post.sched_mp.spec_index(scheduler_ptr).view().queue.map().spec_index(addr) == pre.sched_mp.spec_index(scheduler_ptr).view().queue.map().spec_index(addr)
            }
        &&& forall|s: RwLockSchedulerPtr|
            #![trigger pre.sched_mp.spec_index(s)]
            #![trigger post.sched_mp.spec_index(s)]
            pre.sched_mp.dom().contains(s) && s != scheduler_ptr ==>
                post.sched_mp.spec_index(s) == pre.sched_mp.spec_index(s)
    }

    #[verifier::spinoff_prover]
    proof fn new_thread_close_subsystems_inv(
        pre: KernelK,
        post: KernelK,
        process_ptr: RwLockProcessPtr,
        staging_thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        scheduler_ptr: RwLockSchedulerPtr,
        page_ptr: PagePtr,
        proc_pagetable: RwLockPageTableRoot,
    )
        requires
            pre.inv(),
            page_ptr_valid(page_ptr),
            post.prc_mp.dom().contains(process_ptr),
            post.thr_mp.dom().contains(page_ptr),
            post.sched_mp.dom().contains(scheduler_ptr),
            post.pg_arr.inv(),
            post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
            post.prc_mp.spec_index(process_ptr).view().owned_threads.wf(),
            post.thr_mp.spec_index(page_ptr).view().inv(),
            post.sched_mp.spec_index(scheduler_ptr).view().queue.wf(),
            new_thread_kernel_transition_framing(pre, post, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, page_ptr, proc_pagetable),
        ensures
            post.subsystems_inv(),
    {
        assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); };
        assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
        assert(process_perms_wf(post.prc_mp)) by { reveal(process_perms_wf); reveal(LinkedList::wf_value_list); };
        assert(thread_perms_wf(post.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_free_quota_pending_empty_unless_wlocked); };
        assert(scheduler_perms_wf(post.sched_mp)) by { reveal(scheduler_perms_wf); };
        assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    }

    #[verifier::spinoff_prover]
    proof fn new_thread_close_memory_management_inv(
        pre: KernelK,
        post: KernelK,
        process_ptr: RwLockProcessPtr,
        staging_thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        scheduler_ptr: RwLockSchedulerPtr,
        page_ptr: PagePtr,
        proc_pagetable: RwLockPageTableRoot,
    )
        requires
            pre.inv(),
            post.subsystems_inv(),
            new_thread_kernel_transition_framing(pre, post, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, page_ptr, proc_pagetable),
        ensures
            post.memory_management_inv(),
    {
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
        };
        assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_page_owner_wf); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
        assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
            reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf);
            page_ptr_valid_imply_page_index_valid();
        };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
        assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };
        assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { reveal(container_pages_wf); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { reveal(process_pages_wf); };
        assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            pre.ctn_mp.spec_index(container_ptr).view().uppertree_seq.view().to_set_ensures();
            reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(KernelK::process_management_inv);
            reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf); reveal(container_process_allocator_quota_1g_wf);
            reveal(container_process_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); reveal(thread_perms_wf);
            lemma_process_effective_quota_4k_fold_sum_eq_forall();
            lemma_process_effective_quota_2m_fold_sum_eq_forall();
            lemma_process_effective_quota_1g_fold_sum_eq_forall();
            lemma_container_thread_quota_folds_insert_zero_forall(
                pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, container_ptr, page_ptr,
                pre.ctn_mp.spec_index(container_ptr).view().uppertree_seq.view().to_set(),
            );
        };
        assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
        assert(post.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
        assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
        assert(hugepage_1g_wf(post.pg_arr)) by { reveal(hugepage_1g_wf); };
        assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_perms_wf); reveal(thread_pages_wf); };
        assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
        assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by {
            vstd::set::axiom_set_ext_equal(post.thr_mp.dom(), pre.thr_mp.dom().insert(page_ptr));
            reveal(thread_staged_pages_2m_wf);
        };
        assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by {
            assert(thread_staged_pages_1g_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
            vstd::set::axiom_set_ext_equal(post.thr_mp.dom(), pre.thr_mp.dom().insert(page_ptr));
            reveal(thread_staged_pages_1g_wf);
        };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
    }

    #[verifier::spinoff_prover]
    proof fn new_thread_close_process_management_inv(
        pre: KernelK,
        post: KernelK,
        process_ptr: RwLockProcessPtr,
        staging_thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        scheduler_ptr: RwLockSchedulerPtr,
        page_ptr: PagePtr,
        proc_pagetable: RwLockPageTableRoot,
    )
        requires
            pre.inv(),
            post.subsystems_inv(),
            new_thread_kernel_transition_framing(pre, post, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, page_ptr, proc_pagetable),
        ensures
            post.process_management_inv(),
    {
        assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(post.rt_ctn, pre.ctn_mp, post.ctn_mp); };
        assert({
            &&& pre.ctn_mp.dom().contains(pre.rt_ctn)
            &&& post.ctn_mp.dom().contains(post.rt_ctn)
            &&& pre.ctn_mp.spec_index(pre.rt_ctn).view().root_process_in_processes()
            &&& post.ctn_mp.spec_index(post.rt_ctn).view().root_process_in_processes()
        }) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(container_root_wf); };
        assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
            reveal(per_container_process_tree_wf); reveal(container_process_wf);
            process_no_change_to_tree_fields_imply_wf_forall();
        };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); };
        assert(container_cpu_wf(post.ctn_mp, post.cpu_arr)) by { reveal(container_cpu_wf); };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
        assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by {
            vstd::set::axiom_set_ext_equal(post.thr_mp.dom(), pre.thr_mp.dom().insert(page_ptr));
            reveal(thread_endpoint_ref_counter_wf);
        };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_perms_wf); reveal(thread_endpoint_queue_wf); };
        assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by {
            pre.ctn_mp.spec_index(container_ptr).view().uppertree_seq.view().to_set_ensures();
            reveal(container_thread_wf);
        };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by {
            reveal(container_thread_scheduler_wf); reveal(container_thread_wf); reveal(container_scheduler_wf);
            assert(pre.sched_mp.spec_index(scheduler_ptr).view().queue.wf()) by { reveal(scheduler_perms_wf); };
            seq_push_lemma::<RwLockThreadPtr>();
        };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
        assert(process_empty_thread_list_wlocked(post.prc_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(process_thread_wf); reveal(process_empty_thread_list_wlocked); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by {
            assert(pre.prc_mp.spec_index(process_ptr).view().owned_threads.wf()) by { reveal(process_perms_wf); };
            seq_push_lemma::<RwLockThreadPtr>();
            reveal(container_process_wf); reveal(process_pagetable_match); reveal(process_thread_wf);
        };
    }

    #[verifier::spinoff_prover]
    proof fn new_thread_close_kernel_inv(
        pre: KernelK,
        post: KernelK,
        process_ptr: RwLockProcessPtr,
        staging_thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        scheduler_ptr: RwLockSchedulerPtr,
        page_ptr: PagePtr,
        proc_pagetable: RwLockPageTableRoot,
    )
        requires
            pre.inv(),
            page_ptr_valid(page_ptr),
            post.prc_mp.dom().contains(process_ptr),
            post.thr_mp.dom().contains(page_ptr),
            post.sched_mp.dom().contains(scheduler_ptr),
            post.pg_arr.inv(),
            post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().inv(),
            post.prc_mp.spec_index(process_ptr).view().owned_threads.wf(),
            post.thr_mp.spec_index(page_ptr).view().inv(),
            post.sched_mp.spec_index(scheduler_ptr).view().queue.wf(),
            new_thread_kernel_transition_framing(pre, post, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, page_ptr, proc_pagetable),
        ensures
            post.inv(),
    {
        new_thread_close_subsystems_inv(pre, post, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, page_ptr, proc_pagetable);
        new_thread_close_memory_management_inv(pre, post, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, page_ptr, proc_pagetable);
        new_thread_close_process_management_inv(pre, post, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, page_ptr, proc_pagetable);
        assert(cpu_dirty_map_wf(post.ctn_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); };
        assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr)) by { reveal(tlb_wf_spec); };
        assert(iommu_root_table_process_wf(&post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
        assert(process_pci_function_ownership_wf(&post.irt, post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
        assert(iommu_tlb_wf_spec(post.iommu_tlb, &post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); };
    }

    /// Add t_ptr to dc's owned_threads + ancestors' owned_indirect_threads.
    proof fn add_thread_to_container_sets(
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
            final(container_map).spec_index(dc).view_user_ghost().owned_threads.view() =~= old(container_map).spec_index(dc).view_user_ghost().owned_threads.view().insert(t_ptr),
            forall|c: RwLockContainerPtr|
                #![trigger old(container_map).spec_index(c).view_user_ghost().owned_threads]
                #![trigger final(container_map).spec_index(c).view_user_ghost().owned_threads]
                old(container_map).dom().contains(c) && c != dc ==>
                    final(container_map).spec_index(c).view_user_ghost().owned_threads == old(container_map).spec_index(c).view_user_ghost().owned_threads,
            forall|c: RwLockContainerPtr|
                #![trigger old(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads]
                #![trigger final(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads]
                uppers.to_set().contains(c) ==>
                    final(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads.view() =~= old(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads.view().insert(t_ptr),
            forall|c: RwLockContainerPtr|
                #![trigger old(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads]
                #![trigger final(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads]
                old(container_map).dom().contains(c) && !uppers.to_set().contains(c) ==>
                    final(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads == old(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads,
            container_pcid_allocator_fields_unchanged(*old(container_map), *final(container_map)),
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
        add_thread_to_ancestor_sets(container_map, t_ptr, uppers);
    }

    /// Recursive helper: insert t_ptr into ancestors' owned_indirect_threads.
    proof fn add_thread_to_ancestor_sets(
        tracked container_map: &mut ContainerLockedMap,
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
            forall|c: RwLockContainerPtr| #![auto]
                uppers.to_set().contains(c) ==>
                    final(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads.view() =~= old(container_map).spec_index(c).view_kernel_ghost().owned_indirect_threads.view().insert(t_ptr),
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) && !uppers.to_set().contains(c) ==>
                    final(container_map).spec_index(c).view_kernel_ghost() == old(container_map).spec_index(c).view_kernel_ghost(),
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) ==>
                    final(container_map).spec_index(c).view_user_ghost() == old(container_map).spec_index(c).view_user_ghost(),
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
            assert(uppers.to_set().contains(c0)) by { uppers.to_set_ensures(); };
            container_map.update_kernel_ghost(c0, ContainerGhostK { owned_indirect_threads: Ghost(container_map.spec_index(c0).view_kernel_ghost().owned_indirect_threads.view().insert(t_ptr)) });
            assert(uppers.drop_first().to_set().subset_of(container_map.dom())) by {
                uppers.to_set_ensures();
                uppers.drop_first().to_set_ensures();
                broadcast use vstd::seq_lib::lemma_seq_subrange_elements;
            };
            add_thread_to_ancestor_sets(container_map, t_ptr, uppers.drop_first());
            assert(!uppers.drop_first().to_set().contains(c0)) by {
                uppers.drop_first().to_set_ensures();
                if uppers.drop_first().contains(c0) {
                    let k = choose|k: int| 0 <= k < uppers.drop_first().len() && uppers.drop_first().spec_index(k) == c0;
                }
            };
            assert_sets_equal!(
                uppers.to_set() == uppers.drop_first().to_set().insert(c0),
                c => {
                    uppers.to_set_ensures();
                    uppers.drop_first().to_set_ensures();
                    if uppers.contains(c) && c != c0 {
                        let i = choose|i: int| 0 <= i < uppers.len() && uppers.spec_index(i) == c;
                        assert({
                            &&& i > 0
                            &&& uppers.drop_first().spec_index(i - 1) == c
                        }) by { uppers.to_set_ensures(); };
                    }
                    if uppers.drop_first().contains(c) {
                        let i = choose|i: int| 0 <= i < uppers.drop_first().len() && uppers.drop_first().spec_index(i) == c;
                        assert(uppers.spec_index(i + 1) == c) by { uppers.drop_first().to_set_ensures(); };
                    }
                }
            );
        }
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
        &&& new_u.process_map.spec_index(process_ptr).quota_4k == old_u.process_map.spec_index(process_ptr).quota_4k
        &&& new_u.process_map.spec_index(process_ptr).owned_threads.len() == old_u.process_map.spec_index(process_ptr).owned_threads.len() + 1
        &&& new_u.process_map.spec_index(process_ptr).owned_threads.subrange(0, old_u.process_map.spec_index(process_ptr).owned_threads.len() as int) == old_u.process_map.spec_index(process_ptr).owned_threads
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
