use vstd::prelude::*;
use crate::*;
use super::syscall_new_thread_spec::*;
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
                kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
                kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
                old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
                old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
                old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
                old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
                kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
                old(krnl).thr_mp.dom().contains(current_thread_ptr),
                old(krnl).ctn_mp.dom().contains(container_ptr),
                cpu_lock_perm.view().state() is WriteLock,
                cpu_lock_perm.view().thread_id() == lctx.thread_id(),
                cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
                old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
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
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
                old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
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
                held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                final(lctx).no_locks_held(),
                final(krnl).all_objects_unlocked(final(lctx)),
                final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
                final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
                final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
                final(steps).snapshot_k() == *final(krnl),
                new_thread_step_pre(final(steps).nonlock_view().last().old_u, cpu_id),
                new_thread_step(
                    final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id,
                    final(steps).nonlock_view().last().new_u.process_map.spec_index(process_ptr).owned_threads.last(), *initial_regs, None,
                ),
        {
            let tracked mut process_lock_perm = process_lock_perm.get();
            let tracked mut current_thread_lock_perm = current_thread_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            let tracked scheduler_lock_perm = scheduler_lock_perm.get();

            proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
            let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page_k(
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
                assert(kernel_new_thread_fields(
                    &steps.snapshot_k(), krnl, process_ptr, current_thread_ptr, container_ptr, new_thread_ptr, *initial_regs, None,
                )) by { reveal(kernel_new_thread_fields); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
                steps.end_kernel_step_new_thread_on_cpu(&*krnl, &*lctx, cpu_id, process_ptr, current_thread_ptr, container_ptr, new_thread_ptr, *initial_regs, None, 0);
                assert({
                    &&& new_thread_step_pre(steps.nonlock_view().last().old_u, cpu_id)
                    &&& new_thread_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, new_thread_ptr, *initial_regs, None)
                }) by { reveal(kernel_u_new_thread_changed); };
            }
        }
}
