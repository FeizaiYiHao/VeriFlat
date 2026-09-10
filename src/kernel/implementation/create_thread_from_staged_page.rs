use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;
verus! {

        /// Consume a staged page to create a scheduled thread in `process_ptr`.
        pub fn create_thread_from_staged_page_merged(
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
                old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
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
                ret.0 != staging_thread_ptr,
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
                final(krnl).thr_mp.spec_index(page_ptr).view().owning_proc == process_ptr,
                final(krnl).thr_mp.spec_index(page_ptr).view().endpoint_descriptors.spec_index(0) is None,
                final(krnl).thr_mp.spec_index(page_ptr).view().endpoint_descriptors.wf(),
                final(krnl).thr_mp.spec_index(page_ptr).being_killed() == false,
                final(krnl).prc_mp.dom().contains(process_ptr),
                final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
                final(krnl).prc_mp.spec_index(process_ptr).view_rodata()
                    == old(krnl).prc_mp.spec_index(process_ptr).view_rodata(),
                final(krnl).prc_mp.spec_index(process_ptr).wlocked_by(final(lctx)),
                final(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
                final(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view() == old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().push(page_ptr),
                forall|p: RwLockProcessPtr|
                    #![trigger final(krnl).prc_mp.spec_index(p).locking_thread()]
                    old(krnl).prc_mp.dom().contains(p) && p != process_ptr ==>
                        final(krnl).prc_mp.spec_index(p).locking_thread() == old(krnl).prc_mp.spec_index(p).locking_thread(),
                forall|p: RwLockProcessPtr|
                    #![trigger final(krnl).prc_mp.spec_index(p).being_killed()]
                    old(krnl).prc_mp.dom().contains(p) && p != process_ptr ==>
                        final(krnl).prc_mp.spec_index(p).being_killed() == old(krnl).prc_mp.spec_index(p).being_killed(),
                forall|p: RwLockProcessPtr|
                    #![trigger final(krnl).prc_mp.spec_index(p).view().owned_threads]
                    old(krnl).prc_mp.dom().contains(p) && p != process_ptr ==>
                        final(krnl).prc_mp.spec_index(p).view().owned_threads == old(krnl).prc_mp.spec_index(p).view().owned_threads,
                final(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_clean(),
                final(krnl).thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
                final(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k
                    == old(krnl).thr_mp.spec_index(staging_thread_ptr)
                        .view().quota_4k - 1,
                final(krnl).thr_mp.spec_index(staging_thread_ptr).view().state == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().state,
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
                final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
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
                final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
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
                final(krnl).cpu_set_mp == old(krnl).cpu_set_mp,
                final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
                final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
                final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
                final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
                final(krnl).ctn_mp.spec_index(container_ptr).view_rodata()
                    == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
                final(krnl).ctn_mp.spec_index(container_ptr).view().owned_processes == old(krnl).ctn_mp.spec_index(container_ptr).view().owned_processes,
                forall|c: RwLockContainerPtr|
                    #![trigger final(krnl).ctn_mp.spec_index(c)
                        .view().owned_processes]
                    old(krnl).ctn_mp.dom().contains(c) ==>
                        final(krnl).ctn_mp.spec_index(c)
                            .view().owned_processes
                        == old(krnl).ctn_mp.spec_index(c)
                            .view().owned_processes,
                forall|c: RwLockContainerPtr|
                    #![trigger final(krnl).ctn_mp.spec_index(c).being_killed()]
                    old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed(),
                forall|c: RwLockContainerPtr|
                    #![trigger final(krnl).ctn_mp.spec_index(c).locking_thread()]
                    old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread(),
                forall|c_ptr: RwLockContainerPtr|
                    #![trigger final(krnl).ctn_mp.spec_index(c_ptr).view_ghost().subtree_set]
                    old(krnl).ctn_mp.dom().contains(c_ptr) ==> final(krnl).ctn_mp.spec_index(c_ptr).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c_ptr).view_ghost().subtree_set,
                forall|c_ptr: RwLockContainerPtr|
                    #![trigger final(krnl).ctn_mp.spec_index(c_ptr).view_ghost().uppertree_seq]
                    old(krnl).ctn_mp.dom().contains(c_ptr) ==> final(krnl).ctn_mp.spec_index(c_ptr).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c_ptr).view_ghost().uppertree_seq,
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
        {
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
                    krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().no_duplicates()
                    && !krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set().contains(container_ptr)
                ) by {
                    krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
                    reveal(container_perms_wf); reveal(container_uppertree_seq_wf); reveal(container_tree_fields_wf);
                };
                assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() < usize::MAX) by {
                    let threads = krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view();
                    assert(threads.no_duplicates()) by { reveal(process_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); };
                    reveal(process_thread_wf);
                    lemma_kernel_object_ptr_seq_len_bounded(&*krnl, threads);
                };
                assert(krnl.sched_mp.spec_index(scheduler_ptr).view().queue.view().len() < usize::MAX) by {
                    let threads = krnl.sched_mp.spec_index(scheduler_ptr).view().queue.view();
                    assert(threads.no_duplicates()) by { reveal(scheduler_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); };
                    reveal(container_thread_scheduler_wf);
                    lemma_kernel_object_ptr_seq_len_bounded(&*krnl, threads);
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
            let thread_value = Thread::new_fresh(container_ptr, container_depth, process_ptr, process_depth, proc_pagetable, Ghost(krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view()));
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
                assert(krnl.thr_mp.view().spec_index(staging_thread_ptr).is_init() && krnl.thr_mp.view().spec_index(staging_thread_ptr).addr() == staging_thread_ptr) by { reveal(thread_perms_wf); };
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
                ) by { reveal(thread_perms_wf); };
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
                let uppers = old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
                assert(uppers.to_set().subset_of(krnl.ctn_mp.dom())) by {
                    uppers.to_set_ensures();
                    reveal(container_uppertree_seq_wf);
                };
                krnl.ctn_mp.update_ghost(container_ptr, ContainerGhost {
                    uppertree_seq: krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq,
                    subtree_set: krnl.ctn_mp.spec_index(container_ptr).view_ghost().subtree_set,
                    owned_threads: Ghost(krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().insert(page_ptr)),
                    owned_indirect_threads: krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_indirect_threads,
                });
                add_thread_to_ancestor_sets(&mut krnl.ctn_mp, page_ptr, uppers);
                lctx.update_lock_id(KernelObjId::Thread(page_ptr), fresh_thread_lock_id, krnl.thr_mp.lock_id_by_key(page_ptr));
                assert_seqs_equal!(
                    kernel_k_to_kernel_u(*krnl).process_map.spec_index(process_ptr).owned_threads.subrange(0, kernel_k_to_kernel_u(*old(krnl)).process_map.spec_index(process_ptr).owned_threads.len() as int)
                        == kernel_k_to_kernel_u(*old(krnl)).process_map.spec_index(process_ptr).owned_threads,
                    i => {
                        seq_subrange_split_lemma::<RwLockThreadPtr>();
                    }
                );
                assert(krnl.inv()) by {
                    assert(page_array_wf(krnl.pg_arr)) by { reveal(page_array_wf); };
                    assert(container_perms_wf(krnl.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                    assert(process_perms_wf(krnl.prc_mp)) by { reveal(process_perms_wf); };
                    assert(thread_perms_wf(krnl.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                    assert(scheduler_perms_wf(krnl.sched_mp)) by { reveal(scheduler_perms_wf); };
                    assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                    assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { reveal(container_page_owner_wf); };
                    assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
                    assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by {
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf);
                    };
                    assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
                    assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };

                    assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { reveal(container_pages_wf); };
                    assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { reveal(process_pages_wf); };
                    assert(scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr)) by { reveal(scheduler_pages_wf); };
                    assert(container_process_allocator_quota_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
                        reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf); reveal(container_process_allocator_quota_1g_wf);
                        reveal(container_process_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); reveal(thread_perms_wf);
                        lemma_process_effective_quota_4k_fold_sum_eq_forall();
                        lemma_process_effective_quota_2m_fold_sum_eq_forall();
                        lemma_process_effective_quota_1g_fold_sum_eq_forall();
                        lemma_container_thread_quota_folds_insert_zero_forall(
                            old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, container_ptr, page_ptr,
                            old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set(),
                        );
                    };
                    assert(container_allocator_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_allocator_wf); };
                    assert(krnl.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
                    assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { reveal(process_pagetable_match); };
                    assert(process_iommu_table_match(krnl.prc_mp, krnl.it_mp)) by { reveal(process_iommu_table_match); };
                    assert(hugepage_2m_wf(krnl.pg_arr)) by { reveal(hugepage_2m_wf); };
                    assert(hugepage_1g_wf(krnl.pg_arr)) by { reveal(hugepage_1g_wf); };
                    assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
                    assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_perms_wf); reveal(thread_pages_wf); };
                    assert(thread_staged_pages_4k_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
                    assert(thread_staged_pages_2m_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
                    assert(thread_staged_pages_1g_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_1g_wf); };
                    assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { reveal(endpoint_pages_wf); };
                    assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
                    assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); };
                    assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
                    assert(container_tree_wf(krnl.rt_ctn, krnl.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(krnl.rt_ctn, old(krnl).ctn_mp, krnl.ctn_mp); };
                    assert({
                        &&& old(krnl).ctn_mp.dom().contains(old(krnl).rt_ctn)
                        &&& krnl.ctn_mp.dom().contains(krnl.rt_ctn)
                        &&& old(krnl).ctn_mp.spec_index(old(krnl).rt_ctn).view().root_process_in_processes()
                        &&& krnl.ctn_mp.spec_index(krnl.rt_ctn).view().root_process_in_processes()
                    }) by { reveal(container_root_wf); };
                    assert(container_process_wf(krnl.ctn_mp, krnl.prc_mp)) by { reveal(container_process_wf); };
                    assert(per_container_process_tree_wf(krnl.ctn_mp, krnl.prc_mp)) by {
                        reveal(per_container_process_tree_wf); reveal(container_process_wf);
                        process_no_change_to_tree_fields_imply_wf_forall();
                    };
                    assert(container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); };
                    assert(container_cpu_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr)) by { reveal(container_cpu_wf); };
                    assert(container_scheduler_wf(krnl.ctn_mp, krnl.sched_mp)) by { reveal(container_scheduler_wf); };
                    assert(container_pcid_allocator_wf(krnl.ctn_mp, krnl.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };

                    assert(process_cpu_wf(krnl.prc_mp, krnl.cpu_arr)) by { reveal(process_cpu_wf); };
                    assert(process_pcid_allocator_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
                    assert(thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)) by {
                        vstd::set::axiom_set_ext_equal(krnl.thr_mp.dom(), old(krnl).thr_mp.dom().insert(page_ptr));
                        reveal(thread_endpoint_ref_counter_wf);
                    };
                    assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_perms_wf); reveal(thread_endpoint_queue_wf); };
                    assert(thread_caller_callee_wf(krnl.thr_mp)) by { reveal(thread_caller_callee_wf); };
                    assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf); };
                    assert(container_thread_wf(krnl.ctn_mp, krnl.thr_mp)) by {
                        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
                        reveal(container_thread_wf);
                    };
                    assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by {
                        reveal(container_thread_scheduler_wf); reveal(container_thread_wf); reveal(container_scheduler_wf);
                        assert(old(krnl).sched_mp.spec_index(scheduler_ptr).view().queue.wf()) by { reveal(scheduler_perms_wf); };
                        seq_push_lemma::<RwLockThreadPtr>();
                    };
                    assert(thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)) by { reveal(thread_cpu_wf); };
                    assert(process_empty_thread_list_wlocked(krnl.prc_mp)) by { reveal(process_thread_wf); reveal(process_empty_thread_list_wlocked); };
                    assert(process_thread_wf(krnl.prc_mp, krnl.thr_mp)) by {
                        assert(old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.wf()) by { reveal(process_perms_wf); };
                        seq_push_lemma::<RwLockThreadPtr>();
                        reveal(container_process_wf); reveal(process_pagetable_match); reveal(process_thread_wf);
                    };
                    assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); };
                    assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr)) by { reveal(tlb_wf_spec); };
                    assert(iommu_root_table_process_wf(&krnl.irt, krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_root_table_process_wf); };
                    assert(process_pci_function_ownership_wf(&krnl.irt, krnl.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
                    assert(iommu_tlb_wf_spec(krnl.iommu_tlb, &krnl.irt, krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_tlb_wf_spec); };
                };
            }
            (page_ptr, Tracked(thread_perm))
        }

    /// Insert t_ptr into ancestors' owned_indirect_threads.
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
                    final(container_map).spec_index(c).view_ghost().owned_indirect_threads.view() =~= old(container_map).spec_index(c).view_ghost().owned_indirect_threads.view().insert(t_ptr),
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) && !uppers.to_set().contains(c) ==>
                    final(container_map).spec_index(c).view_ghost().owned_indirect_threads == old(container_map).spec_index(c).view_ghost().owned_indirect_threads,
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) ==>
                    final(container_map).spec_index(c).view_ghost().owned_threads == old(container_map).spec_index(c).view_ghost().owned_threads,
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) ==>
                    final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view()
                    && final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata()
                    && final(container_map).spec_index(c).view_ghost().uppertree_seq == old(container_map).spec_index(c).view_ghost().uppertree_seq
                    && final(container_map).spec_index(c).view_ghost().subtree_set == old(container_map).spec_index(c).view_ghost().subtree_set
                    && final(container_map).spec_index(c).is_init() == old(container_map).spec_index(c).is_init()
                    && final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread()
                    && final(container_map).spec_index(c).being_killed() == old(container_map).spec_index(c).being_killed(),
        decreases uppers.len(),
    {
        if uppers.len() > 0 {
            let c0 = uppers.spec_index(0);
            assert(uppers.to_set().contains(c0)) by { uppers.to_set_ensures(); };
            container_map.update_ghost(c0, ContainerGhost {
                uppertree_seq: container_map.spec_index(c0).view_ghost().uppertree_seq,
                subtree_set: container_map.spec_index(c0).view_ghost().subtree_set,
                owned_threads: container_map.spec_index(c0).view_ghost().owned_threads,
                owned_indirect_threads: Ghost(container_map.spec_index(c0).view_ghost().owned_indirect_threads.view().insert(t_ptr)),
            });
            assert(uppers.drop_first().to_set().subset_of(container_map.dom())) by {
                uppers.to_set_ensures();
                uppers.drop_first().to_set_ensures();
                broadcast use vstd::seq_lib::lemma_seq_subrange_elements;
            };
            add_thread_to_ancestor_sets(container_map, t_ptr, uppers.drop_first());
            assert({
                &&& !uppers.drop_first().to_set().contains(c0)
                &&& uppers.to_set() =~= uppers.drop_first().to_set().insert(c0)
            }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        }
    }

    pub open spec fn kernel_u_new_thread_changed(
        old_u: KernelU,
        new_u: KernelU,
        process_ptr: RwLockProcessPtr,
    ) -> bool {
        &&& new_u.cpu_array == old_u.cpu_array
        &&& new_u.process_map.dom() == old_u.process_map.dom()
        &&& old_u.process_map.dom().contains(process_ptr)
        &&& new_u.process_map.spec_index(process_ptr).quota_4k == old_u.process_map.spec_index(process_ptr).quota_4k
        &&& new_u.process_map.spec_index(process_ptr).owned_threads.len() == old_u.process_map.spec_index(process_ptr).owned_threads.len() + 1
        &&& new_u.process_map.spec_index(process_ptr).owned_threads.subrange(0, old_u.process_map.spec_index(process_ptr).owned_threads.len() as int) == old_u.process_map.spec_index(process_ptr).owned_threads
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
        &&& forall|p: RwLockProcessPtr|
            #![trigger new_u.process_map.spec_index(p)]
            old_u.process_map.dom().contains(p) && p != process_ptr ==>
                new_u.process_map.spec_index(p) == old_u.process_map.spec_index(p)
    }
}
