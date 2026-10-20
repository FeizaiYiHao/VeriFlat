use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::attach_endpoint_reference_and_unlock_eof::{attach_endpoint_reference_and_unlock_eof, attach_endpoint_reference_and_unlock_eof_transition_framing};

verus! {
    pub fn attach_endpoint_reference_and_unlock(
        krnl: &mut KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, current_thread_ptr: RwLockThreadPtr,
        Tracked(lctx): Tracked<&mut LocalContext>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
    )
        requires
            old(krnl).inv(),
            old(krnl).thr_mp.dom().contains(current_thread_ptr),
            !(old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is KILLED),
            current_thread_ptr != thread_ptr,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).is_init(),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED,
            old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.wf(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
            old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(0) is None,
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            {
                ||| old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container
                ||| old(krnl).ctn_mp.spec_index(old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container)
            },
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, thread_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().update(0, Some(endpoint_ptr)),
            final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { endpoint_descriptors: final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
            final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().insert((thread_ptr, 0usize)),
            final(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view() == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view(),
            final(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state,
            final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container == old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container,
            final(krnl).ep_mp.spec_index(endpoint_ptr).being_killed() == old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed(),
            final(krnl).ep_mp.spec_index(endpoint_ptr).view().rf_counter == old(krnl).ep_mp.spec_index(endpoint_ptr).view().rf_counter + 1,
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() is None,
            final(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
            final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            final(krnl).ep_mp.lock_id_by_key(endpoint_ptr) == old(krnl).ep_mp.lock_id_by_key(endpoint_ptr),
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
            final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, endpoint_ptr),
            *final(krnl) == (KernelK { thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, ..*old(krnl) }),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map().remove(thread_ptr),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map().remove(endpoint_ptr),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
    {
        proof {
            assert({
                &&& !krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((thread_ptr, 0))
                &&& krnl.ep_mp.spec_index(endpoint_ptr).view().rf_counter < usize::MAX
            }) by { thread_endpoint_ref_counter_wf_endpoint_at(krnl.thr_mp, krnl.ep_mp, endpoint_ptr, thread_ptr, 0); endpoint_ref_counter_bounded(&*krnl, endpoint_ptr); };
        }
        proof { assert(krnl.thr_mp.perms_wf()) by { thread_perms_wf_map(krnl.thr_mp); }; assert(krnl.ep_mp.perms_wf() && krnl.ep_mp.spec_index(endpoint_ptr).is_init()) by { endpoint_perms_wf_map(krnl.ep_mp); endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr); }; }
        {
            let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
            thread_mut.endpoint_descriptors.set(0, Some(endpoint_ptr));
        } {
            let endpoint_mut = krnl.ep_mp.borrow_mut_typed(endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm));
            endpoint_mut.rf_counter = endpoint_mut.rf_counter + 1;
            endpoint_mut.owning_threads = Ghost(endpoint_mut.owning_threads.view().insert((thread_ptr, 0)));
        }

        proof {
            assert(attach_endpoint_reference_and_unlock_eof_transition_framing(*old(krnl), *krnl, thread_ptr, endpoint_ptr)) by { reveal(attach_endpoint_reference_and_unlock_eof_transition_framing); };
            attach_endpoint_reference_and_unlock_eof(*old(krnl), *krnl, thread_ptr, endpoint_ptr);
        }
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
    }
}
