use vstd::prelude::*;
use crate::*;
use super::syscall_alloc_quota_helpers::{commit_alloc_quota_2m, commit_alloc_quota_4k, commit_alloc_thread_quota_2m, commit_alloc_thread_quota_4k};
use super::syscall_alloc_quota_spec::*;
use super::syscall_alloc_quota_trace::*;

verus! {
        pub fn syscall_alloc_quota_4k(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(krnl).inv(),
                cpu_id == old(lctx).cpu_id(),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).no_locks_held(),
                old(krnl).all_objects_unlocked(old(lctx)),
                old(steps).nonlock_view().len() == 0,
                old(steps).snapshot_k() == *old(krnl),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
                final(steps).snapshot_k() == *final(krnl),
                old(steps).view().len() <= final(steps).view().len(),
                forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
                alloc_quota_4k_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, alloc_amount, ret),
                final(krnl).all_objects_unlocked(final(lctx)),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                final(lctx).no_locks_held(),
                ret == alloc_quota_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount),
                !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
                ret is Success && alloc_amount == 0 ==> final(steps).nonlock_view().len() == 0,
                ret is Success && alloc_amount > 0 ==> {
                    let step = final(steps).nonlock_view()[0];
                    &&& final(steps).nonlock_view().len() == 1
                    &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                    &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                    &&& alloc_quota_4k_step_pre(step.old_u, cpu_id, alloc_amount)
                    &&& alloc_quota_4k_step(step.old_u, step.new_u, cpu_id, alloc_amount)
                },
        {
            proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
            proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }

            let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
            if cpu_lock_res.is_none() {
                proof {
                    alloc_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::CpuIdle);
                    alloc_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::CpuIdle);
                }
                return RetValueType::CpuIdle;
            }
            let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
            assert(
                {   &&& krnl.ctn_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container)
                    &&& krnl.ctn_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container).view_ghost().owned_processes.view()
                        .contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap())
                    &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some
                    &&& krnl.prc_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap())
                    &&& krnl.prc_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap()).view_rodata().view().owning_container
                        == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container
                    &&& krnl.ctn_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
                    &&& krnl.prc_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap()).view_rodata().view().container_depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
                    &&& krnl.prc_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap()).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
                }
            ) by {
                cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id);
                container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
                process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
                container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap());
            };

            let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process().unwrap();
            let container_ptr = cpu.owning_container();
            let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(lctx));
            if container_res.is_none() {
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
                    alloc_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorContainerKilled);
                    alloc_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorContainerKilled);
                }
                return RetValueType::ErrorContainerKilled;
            }
            let Tracked(container_lock_perm) = container_res.unwrap();
            let container = krnl.ctn_mp.borrow_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm));
            if container.zombie {
                krnl.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
                    alloc_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorContainerZombie);
                    alloc_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorContainerZombie);
                }
                return RetValueType::ErrorContainerZombie;
            }
            let container_ro = krnl.ctn_mp.borrow_rodata(container_ptr);
            let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
            assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); };

            let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(lctx));
            if process_res.is_none() {
                krnl.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), None, None, None, None);
                    alloc_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                    alloc_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.unwrap();
            proof { assert(krnl.prc_mp.spec_index(process_ptr).view().state.view() is Running) by {
                thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap());
                process_perms_wf_at(krnl.prc_mp, process_ptr);
            }; }

            let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_4k(alloc_ptr_4k, Tracked(lctx));

            let quota_ref = krnl.allc_4k_mp.borrow_quota_typed(alloc_ptr_4k, Ghost(lctx.allocator_quota_4k_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
            if quota_ref.value < alloc_amount {
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_allocator_quota_4k(alloc_ptr_4k, Tracked(lctx), Tracked(quota_lock_perm));
                krnl.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                    steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                    alloc_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorContainerQuotaInsufficient);
                    alloc_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorContainerQuotaInsufficient);
                }
                return RetValueType::ErrorContainerQuotaInsufficient;
            }

            let process_ref: &Process = krnl.prc_mp.borrow_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm));
            let process_quota_4k = process_ref.quota_4k;
            if alloc_amount > usize::MAX - process_quota_4k {
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_allocator_quota_4k(alloc_ptr_4k, Tracked(lctx), Tracked(quota_lock_perm));
                krnl.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                    steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                    alloc_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorProcessQuotaOverflow);
                    alloc_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorProcessQuotaOverflow);
                }
                return RetValueType::ErrorProcessQuotaOverflow;
            }

            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                alloc_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::Success);
            }
            commit_alloc_quota_4k(krnl, Tracked(lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, alloc_ptr_4k, alloc_amount, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(quota_lock_perm), Tracked(process_lock_perm));
            assert(krnl.all_objects_unlocked(lctx)) by { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); };
            return RetValueType::Success;
        }

        /// Move `alloc_amount` 4K quota from the process running on `cpu_id` to its running thread. The result is
        /// `alloc_thread_quota_4k_syscall_result` of the state at entry.
        pub fn syscall_alloc_thread_quota_4k(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(krnl).inv(),
                cpu_id == old(lctx).cpu_id(),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).no_locks_held(),
                old(krnl).all_objects_unlocked(old(lctx)),
                old(steps).nonlock_view().len() == 0,
                old(steps).snapshot_k() == *old(krnl),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
                final(steps).snapshot_k() == *final(krnl),
                old(steps).view().len() <= final(steps).view().len(),
                forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
                alloc_thread_quota_4k_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, alloc_amount, ret),
                final(krnl).all_objects_unlocked(final(lctx)),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                final(lctx).no_locks_held(),
                ret == alloc_thread_quota_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount),
                !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
                ret is Success && alloc_amount == 0 ==> final(steps).nonlock_view().len() == 0,
                ret is Success && alloc_amount > 0 ==> {
                    let step = final(steps).nonlock_view()[0];
                    &&& final(steps).nonlock_view().len() == 1
                    &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                    &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                    &&& alloc_thread_quota_4k_step_pre(step.old_u, cpu_id, alloc_amount)
                    &&& alloc_thread_quota_4k_step(step.old_u, step.new_u, cpu_id, alloc_amount)
                },
        {
            proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }

            let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
            if cpu_lock_res.is_none() {
                proof {
                    alloc_thread_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::CpuIdle);
                    alloc_thread_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::CpuIdle);
                }
                return RetValueType::CpuIdle;
            }
            let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
            assert({
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some
                &&& krnl.thr_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0).view().state == (ThreadState::RUNNING { cpu_id })
            }) by { thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); };
            let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process().unwrap();
            let thread_ptr = cpu.current_thread().unwrap();
            let container_ptr = cpu.owning_container();
            assert({
                &&& krnl.prc_mp.dom().contains(process_ptr)
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr
                &&& krnl.ctn_mp.dom().contains(container_ptr)
                &&& krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr)
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().container_depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
            }) by {
                process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
                container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
            };

            let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(lctx));
            if process_res.is_none() {
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), None, None, None, None);
                    alloc_thread_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                    alloc_thread_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.unwrap();

            assert({
                &&& krnl.thr_mp.dom().contains(thread_ptr)
                &&& krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr
                &&& krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr
                &&& krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr)
                &&& krnl.prc_mp.spec_index(process_ptr).view().state.view() is Running
                &&& krnl.thr_mp.spec_index(thread_ptr).view().container_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().container_depth
                &&& krnl.thr_mp.spec_index(thread_ptr).view().process_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().depth
            }) by {
                thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr);
                process_perms_wf_at(krnl.prc_mp, process_ptr);
            };
            let thread_res = krnl.wlock_current_running_thread_unless_killed(thread_ptr, Tracked(lctx));
            if thread_res.is_none() {
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
                    alloc_thread_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorThreadKilled);
                    alloc_thread_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorThreadKilled);
                }
                return RetValueType::ErrorThreadKilled;
            }
            let Tracked(thread_lock_perm) = thread_res.unwrap();

            let process_quota_4k = krnl.prc_mp.borrow_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm)).quota_4k;
            if process_quota_4k < alloc_amount {
                krnl.wunlock_thread(thread_ptr, Tracked(lctx), Tracked(thread_lock_perm));
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
                    alloc_thread_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorNoQuota);
                    alloc_thread_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorNoQuota);
                }
                return RetValueType::ErrorNoQuota;
            }

            let thread_quota_4k = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm)).quota_4k;
            if alloc_amount > usize::MAX - thread_quota_4k {
                krnl.wunlock_thread(thread_ptr, Tracked(lctx), Tracked(thread_lock_perm));
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
                    alloc_thread_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorThreadQuotaOverflow);
                    alloc_thread_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorThreadQuotaOverflow);
                }
                return RetValueType::ErrorThreadQuotaOverflow;
            }

            proof { alloc_thread_quota_4k_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::Success); }
            if alloc_amount == 0 {
                krnl.wunlock_thread(thread_ptr, Tracked(lctx), Tracked(thread_lock_perm));
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
                    alloc_thread_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::Success);
                }
                return RetValueType::Success;
            }
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            commit_alloc_thread_quota_4k(krnl, Tracked(lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, alloc_amount, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm));
            assert(krnl.all_objects_unlocked(lctx)) by { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); };
            return RetValueType::Success;
        }

        /// Move `alloc_amount` 2M quota from the container of the process running on `cpu_id` to that process. The
        /// result is `alloc_quota_2m_syscall_result` of the state at entry.
        pub fn syscall_alloc_quota_2m(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(krnl).inv(),
                cpu_id == old(lctx).cpu_id(),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).no_locks_held(),
                old(krnl).all_objects_unlocked(old(lctx)),
                old(steps).nonlock_view().len() == 0,
                old(steps).snapshot_k() == *old(krnl),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
                final(steps).snapshot_k() == *final(krnl),
                old(steps).view().len() <= final(steps).view().len(),
                forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
                alloc_quota_2m_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, alloc_amount, ret),
                final(krnl).all_objects_unlocked(final(lctx)),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                final(lctx).no_locks_held(),
                ret == alloc_quota_2m_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount),
                !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
                ret is Success && alloc_amount == 0 ==> final(steps).nonlock_view().len() == 0,
                ret is Success && alloc_amount > 0 ==> {
                    let step = final(steps).nonlock_view()[0];
                    &&& final(steps).nonlock_view().len() == 1
                    &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                    &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                    &&& alloc_quota_2m_step_pre(step.old_u, cpu_id, alloc_amount)
                    &&& alloc_quota_2m_step(step.old_u, step.new_u, cpu_id, alloc_amount)
                },
        {
            proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
            proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }

            let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
            if cpu_lock_res.is_none() {
                proof {
                    alloc_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::CpuIdle);
                    alloc_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::CpuIdle);
                }
                return RetValueType::CpuIdle;
            }
            let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
            assert(
                {   &&& krnl.ctn_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container)
                    &&& krnl.ctn_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container).view_ghost().owned_processes.view()
                        .contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap())
                    &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some
                    &&& krnl.prc_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap())
                    &&& krnl.prc_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap()).view_rodata().view().owning_container
                        == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container
                    &&& krnl.ctn_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
                    &&& krnl.prc_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap()).view_rodata().view().container_depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
                    &&& krnl.prc_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap()).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
                }
            ) by {
                cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id);
                container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
                process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
                container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap());
            };

            let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process().unwrap();
            let container_ptr = cpu.owning_container();
            let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(lctx));
            if container_res.is_none() {
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
                    alloc_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorContainerKilled);
                    alloc_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorContainerKilled);
                }
                return RetValueType::ErrorContainerKilled;
            }
            let Tracked(container_lock_perm) = container_res.unwrap();
            let container = krnl.ctn_mp.borrow_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm));
            if container.zombie {
                krnl.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
                    alloc_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorContainerZombie);
                    alloc_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorContainerZombie);
                }
                return RetValueType::ErrorContainerZombie;
            }
            let container_ro = krnl.ctn_mp.borrow_rodata(container_ptr);
            let alloc_ptr_2m = container_ro.borrow().allocator_ptr_2m;
            assert(krnl.allc_2m_mp.dom().contains(alloc_ptr_2m)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); };

            let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(lctx));
            if process_res.is_none() {
                krnl.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), None, None, None, None);
                    alloc_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                    alloc_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.unwrap();
            proof { assert(krnl.prc_mp.spec_index(process_ptr).view().state.view() is Running) by {
                thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap());
                process_perms_wf_at(krnl.prc_mp, process_ptr);
            }; }

            let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_2m(alloc_ptr_2m, Tracked(lctx));

            let quota_ref = krnl.allc_2m_mp.borrow_quota_typed(alloc_ptr_2m, Ghost(lctx.allocator_quota_2m_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
            if quota_ref.value < alloc_amount {
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_allocator_quota_2m(alloc_ptr_2m, Tracked(lctx), Tracked(quota_lock_perm));
                krnl.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                    steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                    alloc_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorContainerQuotaInsufficient);
                    alloc_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorContainerQuotaInsufficient);
                }
                return RetValueType::ErrorContainerQuotaInsufficient;
            }

            let process_ref: &Process = krnl.prc_mp.borrow_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm));
            let process_quota_2m = process_ref.quota_2m;
            if alloc_amount > usize::MAX - process_quota_2m {
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_allocator_quota_2m(alloc_ptr_2m, Tracked(lctx), Tracked(quota_lock_perm));
                krnl.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                    steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                    alloc_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorProcessQuotaOverflow);
                    alloc_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorProcessQuotaOverflow);
                }
                return RetValueType::ErrorProcessQuotaOverflow;
            }

            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                alloc_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::Success);
            }
            commit_alloc_quota_2m(krnl, Tracked(lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, alloc_ptr_2m, alloc_amount, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(quota_lock_perm), Tracked(process_lock_perm));
            assert(krnl.all_objects_unlocked(lctx)) by { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); };
            return RetValueType::Success;
        }

        /// Move `alloc_amount` 2M quota from the process running on `cpu_id` to its running thread. The result is
        /// `alloc_thread_quota_2m_syscall_result` of the state at entry.
        pub fn syscall_alloc_thread_quota_2m(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(krnl).inv(),
                cpu_id == old(lctx).cpu_id(),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).no_locks_held(),
                old(krnl).all_objects_unlocked(old(lctx)),
                old(steps).nonlock_view().len() == 0,
                old(steps).snapshot_k() == *old(krnl),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
                final(steps).snapshot_k() == *final(krnl),
                old(steps).view().len() <= final(steps).view().len(),
                forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
                alloc_thread_quota_2m_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, alloc_amount, ret),
                final(krnl).all_objects_unlocked(final(lctx)),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                final(lctx).no_locks_held(),
                ret == alloc_thread_quota_2m_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount),
                !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
                ret is Success && alloc_amount == 0 ==> final(steps).nonlock_view().len() == 0,
                ret is Success && alloc_amount > 0 ==> {
                    let step = final(steps).nonlock_view()[0];
                    &&& final(steps).nonlock_view().len() == 1
                    &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                    &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                    &&& alloc_thread_quota_2m_step_pre(step.old_u, cpu_id, alloc_amount)
                    &&& alloc_thread_quota_2m_step(step.old_u, step.new_u, cpu_id, alloc_amount)
                },
        {
            proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }

            let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
            if cpu_lock_res.is_none() {
                proof {
                    alloc_thread_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::CpuIdle);
                    alloc_thread_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::CpuIdle);
                }
                return RetValueType::CpuIdle;
            }
            let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
            assert({
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some
                &&& krnl.thr_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0).view().state == (ThreadState::RUNNING { cpu_id })
            }) by { thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); };
            let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process().unwrap();
            let thread_ptr = cpu.current_thread().unwrap();
            let container_ptr = cpu.owning_container();
            assert({
                &&& krnl.prc_mp.dom().contains(process_ptr)
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr
                &&& krnl.ctn_mp.dom().contains(container_ptr)
                &&& krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr)
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().container_depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
            }) by {
                process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
                container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
            };

            let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(lctx));
            if process_res.is_none() {
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), None, None, None, None);
                    alloc_thread_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                    alloc_thread_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.unwrap();

            assert({
                &&& krnl.thr_mp.dom().contains(thread_ptr)
                &&& krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr
                &&& krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr
                &&& krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr)
                &&& krnl.prc_mp.spec_index(process_ptr).view().state.view() is Running
                &&& krnl.thr_mp.spec_index(thread_ptr).view().container_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().container_depth
                &&& krnl.thr_mp.spec_index(thread_ptr).view().process_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().depth
            }) by {
                thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr);
                process_perms_wf_at(krnl.prc_mp, process_ptr);
            };
            let thread_res = krnl.wlock_current_running_thread_unless_killed(thread_ptr, Tracked(lctx));
            if thread_res.is_none() {
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
                    alloc_thread_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorThreadKilled);
                    alloc_thread_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorThreadKilled);
                }
                return RetValueType::ErrorThreadKilled;
            }
            let Tracked(thread_lock_perm) = thread_res.unwrap();

            let process_quota_2m = krnl.prc_mp.borrow_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm)).quota_2m;
            if process_quota_2m < alloc_amount {
                krnl.wunlock_thread(thread_ptr, Tracked(lctx), Tracked(thread_lock_perm));
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
                    alloc_thread_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorNoQuota);
                    alloc_thread_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorNoQuota);
                }
                return RetValueType::ErrorNoQuota;
            }

            let thread_quota_2m = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm)).quota_2m;
            if alloc_amount > usize::MAX - thread_quota_2m {
                krnl.wunlock_thread(thread_ptr, Tracked(lctx), Tracked(thread_lock_perm));
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
                    alloc_thread_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorThreadQuotaOverflow);
                    alloc_thread_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorThreadQuotaOverflow);
                }
                return RetValueType::ErrorThreadQuotaOverflow;
            }

            proof { alloc_thread_quota_2m_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::Success); }
            if alloc_amount == 0 {
                krnl.wunlock_thread(thread_ptr, Tracked(lctx), Tracked(thread_lock_perm));
                krnl.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(process_ptr), Some(thread_ptr), None, None, None);
                    alloc_thread_quota_2m_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::Success);
                }
                return RetValueType::Success;
            }
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            commit_alloc_thread_quota_2m(krnl, Tracked(lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, alloc_amount, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm));
            assert(krnl.all_objects_unlocked(lctx)) by { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); };
            return RetValueType::Success;
        }
}
