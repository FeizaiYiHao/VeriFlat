use vstd::prelude::*;
use vstd::assert_seqs_equal;
use vstd::assert_sets_equal;
use crate::*;
#[cfg(feature = "split-crates")]
pub use veriflat_kernel_core::{create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
#[cfg(not(feature = "split-crates"))]
pub use crate::kernel::implementation::create_thread_from_staged_page::{create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
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
                old(krnl).sched_mp.spec_index(scheduler_ptr).wlocked_by(&lctx),
                old(krnl).sched_mp.spec_index(scheduler_ptr).being_killed() == false,
                old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
                process_lock_perm.view().state() is WriteLock,
                process_lock_perm.view().thread_id() == lctx.thread_id(),
                process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(krnl).prc_mp.spec_index(process_ptr).wlocked_by(&lctx),
                old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
                old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                current_thread_lock_perm.view().state() is WriteLock,
                current_thread_lock_perm.view().thread_id() == lctx.thread_id(),
                current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
                old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(&lctx),
                old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1,
                kernel_objects_unlocked_except(old(krnl), old(lctx).thread_id(), set![cpu_id], Set::empty(), set![scheduler_ptr], set![process_ptr], set![current_thread_ptr], Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty()),
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
            krnl.wunlock_thread(new_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm));
            krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
            krnl.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
            krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
            krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

            proof {
                assert(lctx.no_locks_held()) by {  reveal(LocalContext::holds_no_allocator_locks); };
                steps.end_kernel_step(&*krnl, &*lctx);
            }
        }
}
