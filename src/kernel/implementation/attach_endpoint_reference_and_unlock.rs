use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::attach_endpoint_reference_and_unlock_eof::{attach_endpoint_reference_and_unlock_eof, attach_endpoint_reference_and_unlock_eof_transition_framing};

verus! {
    pub fn attach_endpoint_reference_and_unlock(
        krnl: &mut KernelK, thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr, current_thrd_ptr: RwLockThreadPtr,
        Tracked(lctx): Tracked<&mut LocalContext>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
    )
        requires
            old(krnl).inv(),
            old(krnl).thrd_mp.dom().contains(current_thrd_ptr),
            !(old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state is KILLED),
            current_thrd_ptr != thrd_ptr,
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).is_init(),
            old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == false,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().state is SCHEDULED,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.wf(),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
            !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.spec_index(0) is None,
            old(krnl).ep_mp.dom().contains(ep_ptr),
            {
                ||| old(krnl).ep_mp.spec_index(ep_ptr).view().owning_container == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container
                ||| old(krnl).ctn_mp.spec_index(old(krnl).ep_mp.spec_index(ep_ptr).view().owning_container).view_ghost().subtree_set.view().contains(old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container)
            },
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), ep_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(ep_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).thread_lock_map().dom() =~= set![current_thrd_ptr, thrd_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![ep_ptr],
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().update(0, Some(ep_ptr)),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { endpoint_descriptors: final(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
            final(krnl).ep_mp.spec_index(ep_ptr).view().owning_threads.view() == old(krnl).ep_mp.spec_index(ep_ptr).view().owning_threads.view().insert((thrd_ptr, 0usize)),
            final(krnl).ep_mp.spec_index(ep_ptr).view().queue.view() == old(krnl).ep_mp.spec_index(ep_ptr).view().queue.view(),
            final(krnl).ep_mp.spec_index(ep_ptr).view().queue_state == old(krnl).ep_mp.spec_index(ep_ptr).view().queue_state,
            final(krnl).ep_mp.spec_index(ep_ptr).view().owning_container == old(krnl).ep_mp.spec_index(ep_ptr).view().owning_container,
            final(krnl).ep_mp.spec_index(ep_ptr).being_killed() == old(krnl).ep_mp.spec_index(ep_ptr).being_killed(),
            final(krnl).ep_mp.spec_index(ep_ptr).view().rf_counter == old(krnl).ep_mp.spec_index(ep_ptr).view().rf_counter + 1,
            final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() is None,
            final(krnl).ep_mp.spec_index(ep_ptr).locking_thread() is None,
            final(krnl).thrd_mp.lock_id_by_key(thrd_ptr) == old(krnl).thrd_mp.lock_id_by_key(thrd_ptr),
            final(krnl).ep_mp.lock_id_by_key(ep_ptr) == old(krnl).ep_mp.lock_id_by_key(ep_ptr),
            final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
            final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, ep_ptr),
            *final(krnl) == (KernelK { thrd_mp: final(krnl).thrd_mp, ep_mp: final(krnl).ep_mp, ..*old(krnl) }),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map().remove(thrd_ptr),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map().remove(ep_ptr),
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
                &&& !krnl.ep_mp.spec_index(ep_ptr).view().owning_threads.view().contains((thrd_ptr, 0))
                &&& krnl.ep_mp.spec_index(ep_ptr).view().rf_counter < usize::MAX
            }) by { thread_endpoint_ref_counter_wf_endpoint_at(krnl.thrd_mp, krnl.ep_mp, ep_ptr, thrd_ptr, 0); endpoint_ref_counter_bounded(&*krnl, ep_ptr); };
        }
        proof { assert(krnl.thrd_mp.perms_wf()) by { thread_perms_wf_map(krnl.thrd_mp); }; assert(krnl.ep_mp.perms_wf() && krnl.ep_mp.spec_index(ep_ptr).is_init()) by { endpoint_perms_wf_map(krnl.ep_mp); endpoint_perms_wf_at(krnl.ep_mp, ep_ptr); }; }
        {
            let thread_mut = krnl.thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
            thread_mut.endpoint_descriptors.set(0, Some(ep_ptr));
        } {
            let endpoint_mut = krnl.ep_mp.borrow_mut_typed(ep_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm));
            endpoint_mut.rf_counter = endpoint_mut.rf_counter + 1;
            endpoint_mut.owning_threads = Ghost(endpoint_mut.owning_threads.view().insert((thrd_ptr, 0)));
        }

        proof {
            assert(attach_endpoint_reference_and_unlock_eof_transition_framing(*old(krnl), *krnl, thrd_ptr, ep_ptr)) by { reveal(attach_endpoint_reference_and_unlock_eof_transition_framing); };
            attach_endpoint_reference_and_unlock_eof(*old(krnl), *krnl, thrd_ptr, ep_ptr);
        }
        krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_endpoint(ep_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
    }
}
