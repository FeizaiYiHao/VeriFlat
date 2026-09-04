use vstd::prelude::*;
use crate::*;

verus! {

    /// Add the first endpoint descriptor and its reverse reference together.
    pub fn attach_endpoint_reference_and_unlock(
        krnl: &mut KernelK,
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
    )
        requires
            old(krnl).inv(),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_PAGES, page_index),
            old(krnl).sched_mp.dom().contains(scheduler_ptr),
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).thr_mp.dom().contains(current_thread_ptr),
            current_thread_ptr != thread_ptr,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).is_init(),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED,
            old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.wf(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(0) is None,
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            old(krnl).ep_mp.spec_index(endpoint_ptr).is_init(),
            old(krnl).ctn_mp.dom().contains(old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container),
            {
                ||| old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container
                ||| old(krnl).ctn_mp.spec_index(old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container).view().subtree_set.view().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container)
            },
            old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.spec_index(endpoint_ptr).wlocked_by(old(lctx)),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![current_thread_ptr, thread_ptr]),
            endpoint_objects_unlocked_except(old(krnl).ep_mp, old(lctx).thread_id(), set![endpoint_ptr]),
        ensures
            final(krnl).inv(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(0) == Some(endpoint_ptr),
            final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((thread_ptr, 0)),
            final(krnl).ep_mp.spec_index(endpoint_ptr).view().rf_counter == old(krnl).ep_mp.spec_index(endpoint_ptr).view().rf_counter + 1,
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() is None,
            final(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
            final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            final(krnl).ep_mp.lock_id_by_key(endpoint_ptr) == old(krnl).ep_mp.lock_id_by_key(endpoint_ptr),
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
            final(krnl).thr_mp.spec_index(current_thread_ptr) == old(krnl).thr_mp.spec_index(current_thread_ptr),
            final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, endpoint_ptr),
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
            final(krnl).cpu_arr.lock_id_by_index(cpu_id) == old(krnl).cpu_arr.lock_id_by_index(cpu_id),
            final(krnl).sched_mp.lock_id_by_key(scheduler_ptr) == old(krnl).sched_mp.lock_id_by_key(scheduler_ptr),
            final(krnl).prc_mp.lock_id_by_key(process_ptr) == old(krnl).prc_mp.lock_id_by_key(process_ptr),
            final(krnl).thr_mp.lock_id_by_key(current_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(current_thread_ptr),
            final(krnl).pg_arr.lock_id_by_index(page_index) == old(krnl).pg_arr.lock_id_by_index(page_index),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(krnl).thr_mp.lock_id_by_key(thread_ptr), KernelObjId::Thread(thread_ptr))).remove((old(krnl).ep_mp.lock_id_by_key(endpoint_ptr), KernelObjId::Endpoint(endpoint_ptr))),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map().remove(thread_ptr),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map().remove(endpoint_ptr),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![current_thread_ptr]),
            endpoint_objects_unlocked(final(krnl).ep_mp, final(lctx).thread_id()),
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
    {
        proof {
            assert({
                &&& krnl.thr_mp.view().spec_index(thread_ptr).is_init()
                &&& krnl.thr_mp.view().spec_index(thread_ptr).addr() == thread_ptr
                &&& krnl.ep_mp.view().spec_index(endpoint_ptr).is_init()
                &&& krnl.ep_mp.view().spec_index(endpoint_ptr).addr() == endpoint_ptr
                &&& krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.wf()
                &&& krnl.ep_mp.spec_index(endpoint_ptr).inv()
            }) by { reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(endpoints_inv); };
            assert({
                &&& !krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((thread_ptr, 0))
                &&& krnl.ep_mp.spec_index(endpoint_ptr).view().rf_counter < usize::MAX
            }) by {
                reveal(thread_endpoint_ref_counter_wf);
                endpoint_ref_counter_bounded(&*krnl, endpoint_ptr);
            };
        }
        proof {
            assert(krnl.thr_mp.perms_wf()) by { reveal(thread_perms_wf); };
            assert(krnl.ep_mp.perms_wf()) by { reveal(endpoint_perms_wf); };
        }
        {
            let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
            thread_mut.endpoint_descriptors.set(0, Some(endpoint_ptr));
        } {
            let endpoint_mut = krnl.ep_mp.borrow_mut_typed(endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm));
            endpoint_mut.rf_counter = endpoint_mut.rf_counter + 1;
            endpoint_mut.owning_threads = Ghost(endpoint_mut.owning_threads.view().insert((thread_ptr, 0)));
        }

        proof {
            assert(krnl.subsystems_inv()) by {
                assert(thread_perms_wf(krnl.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
                assert(endpoint_perms_wf(krnl.ep_mp)) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); };
                reveal(KernelK::default_pagetable_wf);
            };
            assert(krnl.memory_management_inv()) by { thread_endpoint_no_change_imply_memory_management_inv(*old(krnl), *krnl); };
            assert(krnl.process_management_inv()) by {
                assert(thread_endpoint_reference_added(old(krnl).thr_mp, krnl.thr_mp, thread_ptr, endpoint_ptr, 0)) by { thread_endpoint_reference_added_from_single_update(old(krnl).thr_mp, krnl.thr_mp, thread_ptr, endpoint_ptr, 0); };
                assert(endpoint_reference_added(old(krnl).ep_mp, krnl.ep_mp, thread_ptr, endpoint_ptr, 0)) by { endpoint_reference_added_from_single_update(old(krnl).ep_mp, krnl.ep_mp, thread_ptr, endpoint_ptr, 0); };
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
                &&& krnl.ep_mp.lock_id_by_key(endpoint_ptr) == old(krnl).ep_mp.lock_id_by_key(endpoint_ptr)
                &&& krnl.thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr)
            }) by {
                reveal(thread_perms_wf); reveal(endpoint_perms_wf);
            };
            assert(thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![current_thread_ptr, thread_ptr])) by {
                thread_endpoint_reference_added_from_single_update(old(krnl).thr_mp, krnl.thr_mp, thread_ptr, endpoint_ptr, 0);
                reveal(thread_endpoint_reference_added);
            };
            assert(endpoint_objects_unlocked_except(krnl.ep_mp, lctx.thread_id(), set![endpoint_ptr])) by {
                endpoint_reference_added_from_single_update(old(krnl).ep_mp, krnl.ep_mp, thread_ptr, endpoint_ptr, 0);
                reveal(endpoint_reference_added);
            };
        }
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        proof {
            assert({
                &&& krnl.thr_mp.spec_index(current_thread_ptr) == old(krnl).thr_mp.spec_index(current_thread_ptr)
                &&& krnl.thr_mp.lock_id_by_key(current_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(current_thread_ptr)
            }) by {
                reveal(thread_perms_wf);
                lock_id_fields_eq_imply_eq();
            };
        }
    }

}
