use vstd::prelude::*;
use crate::*;
use super::syscall_new_thread_spec::*;
use super::syscall_new_thread_trace::*;
#[cfg(feature = "split-crates")]
pub use veriflat_kernel_core::{create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
#[cfg(not(feature = "split-crates"))]
pub use crate::kernel::implementation::create_thread_from_staged_page::{create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
verus! {
        /// Commit path: allocate 4k page, create thread, release all locks.
        pub(super) fn add_new_thread_to_proc_container_and_scheduler(
            krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
            process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr,
            process_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>, cpu_lock_perm: Tracked<LockPerm>,
            scheduler_lock_perm: Tracked<LockPerm>, initial_regs: &Registers,
        )
            requires
                index_valid(NUM_CPUS, cpu_id),
                cpu_id == old(lctx).cpu_id(),
                old(krnl).cpu_published[cpu_id as int].view() == (
                    old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3,
                    old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid,
                ),
                old(krnl).inv(),
                *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, sched_mp: old(krnl).sched_mp, ..old(steps).snapshot_k() }),
                old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
                old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
                old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, current_thread_ptr),
                old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
                old(steps).snapshot_k().prc_mp.spec_index(process_ptr).locking_thread() is None,
                old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).locking_thread() is None,
                old(krnl).ep_mp == old(steps).snapshot_k().ep_mp,
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
                final(steps).view().len() == old(steps).view().len() + 2,
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                final(lctx).no_locks_held(),
                final(krnl).all_objects_unlocked(final(lctx)),
                final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 2,
                final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
                final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
                final(steps).snapshot_k() == *final(krnl),
                new_thread_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, *initial_regs, None, true),
                forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        {
            let tracked mut process_lock_perm = process_lock_perm.get();
            let tracked mut current_thread_lock_perm = current_thread_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            let tracked scheduler_lock_perm = scheduler_lock_perm.get();
            krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(Some(SyscallProgress::NewThread { regs: *initial_regs, endpoint_index: None })), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
            proof {
                assert(steps.snapshot_k().thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None) by {
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
                };
                let ghost enter_lctx = *lctx;
                let ghost enter_before = steps.view();
                let ghost entered_k = *krnl;
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
                krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, current_thread_ptr);
                assert(new_thread_trace_after_enter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, *initial_regs, None)) by {
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
                    kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(&old(steps).snapshot_k(), old(krnl), &enter_lctx, cpu_id, process_ptr, current_thread_ptr, None, true, None, false, None);
                    kernel_thread_syscall_progress_changed_implies_u_step(old(krnl), &entered_k, current_thread_ptr);
                    new_thread_enter_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id, process_ptr, current_thread_ptr, container_ptr, None, *initial_regs, None);
                    new_thread_trace_enter_step(&*steps, enter_before, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, *initial_regs, None);
                };
                assert(krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(container_thread_wf); };
            }
            let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page_k(
                krnl, current_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm),
            );
            let page_index = page_ptr2page_index(page_ptr);
            proof {
                assert({
                    &&& kernel_k_to_kernel_u(steps.snapshot_k()).cpu_array[cpu_id as int].lock_state is WriteLocked
                    &&& kernel_k_to_kernel_u(steps.snapshot_k()).process_map.spec_index(process_ptr).lock_state is WriteLocked
                    &&& kernel_k_to_kernel_u(steps.snapshot_k()).thread_map.spec_index(current_thread_ptr).lock_state is WriteLocked
                }) by { kernel_write_held_context_projection(&*krnl, &*lctx, cpu_id, process_ptr, current_thread_ptr, None); };
            }

            proof {
                assert(!krnl.prc_mp.spec_index(process_ptr).view().zombie) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread_ptr); };
                assert(page_ptr != current_thread_ptr) by { reveal(thread_pages_wf); };
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            }
            let (new_thread_ptr, Tracked(new_thread_lock_perm)) = create_thread_from_staged_page_merged(
                krnl, page_ptr, process_ptr, current_thread_ptr, container_ptr, scheduler_ptr, Tracked(&mut *lctx), Tracked(&page_lock_perm),
                Tracked(&process_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&scheduler_lock_perm), initial_regs,
            );
            krnl.wunlock_thread(new_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm));
            krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
            krnl.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
            krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
            krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
            krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));

            proof {
                let ghost finish_k = steps.snapshot_k();
                let ghost finish_before = steps.view();
                assert(kernel_new_thread_fields(
                    &steps.snapshot_k(), krnl, process_ptr, current_thread_ptr, container_ptr, new_thread_ptr, *initial_regs, None, None,
                )) by { reveal(kernel_new_thread_fields); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
                steps.end_kernel_step_new_thread_on_cpu(&*krnl, &*lctx, cpu_id, process_ptr, current_thread_ptr, container_ptr, new_thread_ptr, *initial_regs, None, 0, None);
                assert(new_thread_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
                    kernel_k_to_kernel_u(*krnl), cpu_id, *initial_regs, None, true)) by {
                    reveal(kernel_new_thread_fields);
                    kernel_new_thread_fields_and_unlocks_implies_u_step(&finish_k, &*krnl, cpu_id, process_ptr, current_thread_ptr, container_ptr, new_thread_ptr, *initial_regs, None, None, None);
                    kernel_cpu_thread_projection_at(&finish_k, cpu_id, process_ptr, current_thread_ptr, None);
                    new_thread_finish_step_from_u(kernel_k_to_kernel_u(finish_k), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, current_thread_ptr, container_ptr, new_thread_ptr, None, *initial_regs, None);
                    new_thread_trace_finish_step(&*steps, finish_before, old(steps).view().len() as int, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(finish_k), kernel_k_to_kernel_u(*krnl), cpu_id, *initial_regs, None);
                };
            }
        }
}
