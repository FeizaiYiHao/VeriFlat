use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
pub use veriflat_kernel_core::{create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
#[cfg(not(feature = "split-crates"))]
pub use crate::kernel::implementation::create_thread_from_staged_page::{create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
verus! {

        /// Commit path: allocate 4k page, create thread, release all locks.
        pub(super) fn add_new_thread_to_proc_container_and_scheduler(
            krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr,
            container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr,
            process_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>,
            cpu_lock_perm: Tracked<LockPerm>, scheduler_lock_perm: Tracked<LockPerm>, initial_regs: &Registers,
        )
            requires
                index_valid(NUM_CPUS, cpu_id),
                cpu_id == old(lctx).cpu_id(),
                old(krnl).cpu_published[cpu_id as int].view() == (
                    old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3,
                    old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid,
                ),
                old(krnl).inv(),
                lctx.kernel_view_locking_state() is Acquire,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
                old(krnl).thr_mp.dom().contains(current_thread_ptr),
                old(krnl).ctn_mp.dom().contains(container_ptr),
                cpu_lock_perm.view().state() is WriteLock,
                cpu_lock_perm.view().thread_id() == lctx.thread_id(),
                cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
                old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
                scheduler_lock_perm.view().state() is WriteLock,
                scheduler_lock_perm.view().thread_id() == lctx.thread_id(),
                scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(lctx.scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write),
                old(krnl).sched_mp.spec_index(scheduler_ptr).being_killed() == false,
                old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
                process_lock_perm.view().state() is WriteLock,
                process_lock_perm.view().thread_id() == lctx.thread_id(),
                process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
                old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
                old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                current_thread_lock_perm.view().state() is WriteLock,
                current_thread_lock_perm.view().thread_id() == lctx.thread_id(),
                current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(lctx.thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
                old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1,
                old(lctx).page_lock_map().dom().is_empty(),
                old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
                old(lctx).container_lock_map().dom().is_empty(),
                old(lctx).process_lock_map().dom() =~= set![process_ptr],
                old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
                old(lctx).endpoint_lock_map().dom().is_empty(),
                old(lctx).scheduler_lock_map().dom() =~= set![scheduler_ptr],
                old(lctx).pcid_allocator_lock_map().dom().is_empty(),
                old(lctx).cpu_set_lock_map().dom().is_empty(),
                old(lctx).pagetable_lock_map().dom().is_empty(),
                old(lctx).iommu_table_lock_map().dom().is_empty(),
                old(lctx).pcid_needflush_lock_map().dom().is_empty(),
                old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
                old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
                old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
                old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
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

            let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(
                krnl, current_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps),
                Tracked(&current_thread_lock_perm),
            );
            let page_index = page_ptr2page_index(page_ptr);

            proof {
                assert(!krnl.prc_mp.spec_index(process_ptr).view().zombie) by { reveal(process_thread_wf); };
                assert(page_ptr != current_thread_ptr) by { reveal(thread_pages_wf); };
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            }
            let (new_thread_ptr, Tracked(new_thread_lock_perm)) = create_thread_from_staged_page_merged(
                krnl, page_ptr, process_ptr, current_thread_ptr, container_ptr, scheduler_ptr, Tracked(&mut *lctx),
                Tracked(&page_lock_perm), Tracked(&process_lock_perm), Tracked(&current_thread_lock_perm),
                Tracked(&scheduler_lock_perm), initial_regs,
            );
            krnl.wunlock_thread(new_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm));
            krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
            krnl.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
            krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
            krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

            proof {
                assert(lctx.no_locks_held()) by { reveal(LocalContext::holds_no_allocator_locks); };
                assert(kernel_u_new_thread_changed(steps.snap_shot, kernel_k_to_kernel_u(*krnl), process_ptr)) by { reveal(kernel_k_to_kernel_u); };
                assert(steps.snap_shot != kernel_k_to_kernel_u(*krnl)) by { reveal(kernel_u_new_thread_changed); };
                let ghost step_old_u = steps.snap_shot;
                steps.end_kernel_step(&*krnl, &*lctx);
                assert(steps.steps == old(steps).steps.push(KernelStep {
                    old_u: step_old_u, new_u: kernel_k_to_kernel_u(*krnl),
                })) by { reveal(record_user_view_change); };
            }
        }
}
