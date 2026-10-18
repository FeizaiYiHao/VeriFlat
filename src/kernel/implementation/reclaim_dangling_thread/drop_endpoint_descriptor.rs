use vstd::prelude::*;
use crate::*;

verus! {
/// Release descriptor `index` of an exiting or killed thread: clear it, drop the reference of its write-held endpoint,
/// and release the endpoint.
pub fn drop_endpoint_descriptor(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx,
    Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING || old(krnl).thr_mp.spec_index(thread_ptr).view().state is KILLED,
        old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[index as int] == Some(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        endpoint_lock_perm.state() is WriteLock,
        endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr)),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, ..*old(krnl) }),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { endpoint_descriptors: final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().update(index as int, None),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
        final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, endpoint_ptr),
        final(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view() == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view(),
        final(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state,
        final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container == old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container,
        final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().remove((thread_ptr, index)),
        final(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
        final(krnl).ep_mp.spec_index(endpoint_ptr).being_killed() == old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed(),
{
    proof {
        thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((thread_ptr, index))) by {
            thread_endpoint_ref_counter_wf_thread_at(krnl.thr_mp, krnl.ep_mp, thread_ptr, index);
        };
        endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr);
        vstd::set::lemma_set_remove_len(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view(), (thread_ptr, index));
    }
    {
        let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
        thread_mut.endpoint_descriptors.set(index, None);
    } {
        let endpoint_mut = krnl.ep_mp.borrow_mut_typed(endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm));
        endpoint_mut.rf_counter = endpoint_mut.rf_counter - 1;
        endpoint_mut.owning_threads = Ghost(endpoint_mut.owning_threads.view().remove((thread_ptr, index)));
    }
    proof {
        assert(typed_lock_maps_aligned(krnl, lctx) && krnl.thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr)) by {
            lock_id_fields_eq_imply_eq(); reveal(LockedMap::typed_lock_map_aligned);
        };
        assert(krnl.subsystems_inv()) by {
            assert(thread_perms_wf(krnl.thr_mp)) by {
                reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            };
            assert(endpoint_perms_wf(krnl.ep_mp)) by { reveal(endpoint_perms_wf); };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(krnl.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(*old(krnl), *krnl); };
        assert(krnl.process_management_inv()) by {
            assert(thread_caller_callee_wf(krnl.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(old(krnl).thr_mp, krnl.thr_mp); };
            assert(container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).ep_mp, krnl.ep_mp); };
            assert(thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
            assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_queue_fields(old(krnl).thr_mp, krnl.thr_mp, old(krnl).ep_mp, krnl.ep_mp); };
            assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_thread_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); };
            assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.sched_mp); };
            assert(container_thread_wf(krnl.ctn_mp, krnl.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp); };
            assert(process_thread_wf(krnl.prc_mp, krnl.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(old(krnl).prc_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp); };
            assert(process_emptied_threads_wf(krnl.prc_mp, krnl.thr_mp)) by { reveal(process_emptied_threads_wf); reveal(process_thread_wf); };
            assert(thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).cpu_arr, krnl.cpu_arr); };
        };
    }
    krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
}
} // verus!
