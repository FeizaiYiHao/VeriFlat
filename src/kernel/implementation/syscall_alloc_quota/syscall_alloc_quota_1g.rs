use vstd::prelude::*;
use crate::*;
use super::syscall_alloc_quota_1g_helpers::{commit_alloc_quota_1g, commit_alloc_thread_quota_1g};
use super::syscall_alloc_quota_1g_spec::*;
use super::syscall_alloc_quota_1g_trace::*;

verus! {
        /// Move `alloc_amount` 1G quota from the container of the process running on `cpu_id` to that process. The result is `alloc_quota_1g_syscall_result` of the state at entry.
        pub fn syscall_alloc_quota_1g(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(krnl).inv(),
                cpu_id == old(lctx).cpu_id(),
                old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).no_locks_held(),
                old(krnl).all_objects_unlocked(old(lctx)),
                old(steps).snapshot_k() == *old(krnl),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(steps).snapshot_k() == *final(krnl),
                old(steps).view().len() <= final(steps).view().len(),
                forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
                alloc_quota_1g_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, alloc_amount, ret),
                final(krnl).all_objects_unlocked(final(lctx)),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                final(lctx).no_locks_held(),
                ret == alloc_quota_1g_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount),
        {
            proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }

            let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
            if cpu_lock_res.is_none() {
                proof {
                    alloc_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::CpuIdle);
                    alloc_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::CpuIdle);
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
            let prc_ptr = cpu.current_process().unwrap();
            let ctn_ptr = cpu.owning_container();
            let requested = LockOwnerId::Some(cpu.process_depth());
            let container_res = krnl.wlock_container_unless_killed(ctn_ptr, requested, Tracked(lctx));
            let Tracked(container_lock_perm) = match container_res {
                DynamicWLockResult::Acquired(perm) => perm,
                DynamicWLockResult::Killed(_) => {
                    krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                    proof {
                        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(ctn_ptr), None, None, None, None, None);
                        alloc_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorContainerKilled);
                        alloc_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorContainerKilled);
                    }
                    return RetValueType::ErrorContainerKilled;
                },
                DynamicWLockResult::DepthConflict { .. } => {
                    krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                    proof {
                        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(ctn_ptr), None, None, None, None, None);
                        alloc_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorContainerLockOrderConflict);
                        alloc_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorContainerLockOrderConflict);
                    }
                    return RetValueType::ErrorContainerLockOrderConflict;
                },
            };
            let container = krnl.ctn_mp.borrow_typed(ctn_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm));
            if container.zombie {
                krnl.wunlock_container(ctn_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(ctn_ptr), None, None, None, None, None);
                    alloc_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorContainerZombie);
                    alloc_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorContainerZombie);
                }
                return RetValueType::ErrorContainerZombie;
            }
            let container_ro = krnl.ctn_mp.borrow_rodata(ctn_ptr);
            let alloc_ptr_1g = container_ro.borrow().allocator_ptr_1g;
            assert(krnl.allc_1g_mp.dom().contains(alloc_ptr_1g)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr); };

            let process_res = krnl.wlock_process_unless_killed(prc_ptr, Ghost(cpu_id), Tracked(lctx));
            if process_res.is_none() {
                krnl.wunlock_container(ctn_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(ctn_ptr), Some(prc_ptr), None, None, None, None);
                    alloc_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                    alloc_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.unwrap();
            proof { assert(krnl.prc_mp.spec_index(prc_ptr).view().state.view() is Running) by {
                thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap());
                process_perms_wf_at(krnl.prc_mp, prc_ptr);
            }; }

            let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_1g(alloc_ptr_1g, Tracked(lctx));

            let quota_ref = krnl.allc_1g_mp.borrow_quota_typed(alloc_ptr_1g, Ghost(lctx.allocator_quota_1g_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
            if quota_ref.value < alloc_amount {
                krnl.wunlock_process(prc_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_allocator_quota_1g(alloc_ptr_1g, Tracked(lctx), Tracked(quota_lock_perm));
                krnl.wunlock_container(ctn_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                    steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                    alloc_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorContainerQuotaInsufficient);
                    alloc_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorContainerQuotaInsufficient);
                }
                return RetValueType::ErrorContainerQuotaInsufficient;
            }

            let process_ref: &Process = krnl.prc_mp.borrow_typed(prc_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm));
            let process_quota_1g = process_ref.quota_1g;
            if alloc_amount > usize::MAX - process_quota_1g {
                krnl.wunlock_process(prc_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_allocator_quota_1g(alloc_ptr_1g, Tracked(lctx), Tracked(quota_lock_perm));
                krnl.wunlock_container(ctn_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                    steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                    alloc_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorProcessQuotaOverflow);
                    alloc_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorProcessQuotaOverflow);
                }
                return RetValueType::ErrorProcessQuotaOverflow;
            }

            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                alloc_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::Success);
            }
            commit_alloc_quota_1g(krnl, Tracked(lctx), Tracked(&mut *steps), cpu_id, ctn_ptr, prc_ptr, alloc_ptr_1g, alloc_amount, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(quota_lock_perm), Tracked(process_lock_perm));
            assert(krnl.all_objects_unlocked(lctx)) by { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); };
            return RetValueType::Success;
        }

        /// Move `alloc_amount` 1G quota from the process running on `cpu_id` to its running thread. The result is `alloc_thread_quota_1g_syscall_result` of the state at entry.
        pub fn syscall_alloc_thread_quota_1g(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(krnl).inv(),
                cpu_id == old(lctx).cpu_id(),
                old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).no_locks_held(),
                old(krnl).all_objects_unlocked(old(lctx)),
                old(steps).snapshot_k() == *old(krnl),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(steps).snapshot_k() == *final(krnl),
                old(steps).view().len() <= final(steps).view().len(),
                forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
                alloc_thread_quota_1g_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, alloc_amount, ret),
                final(krnl).all_objects_unlocked(final(lctx)),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                final(lctx).no_locks_held(),
                ret == alloc_thread_quota_1g_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount),
        {
            proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }

            let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
            if cpu_lock_res.is_none() {
                proof {
                    alloc_thread_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::CpuIdle);
                    alloc_thread_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::CpuIdle);
                }
                return RetValueType::CpuIdle;
            }
            let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
            assert({
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some
                &&& krnl.thrd_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0).view().state == (ThreadState::RUNNING { cpu_id })
            }) by { thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); };
            let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
            let prc_ptr = cpu.current_process().unwrap();
            let thrd_ptr = cpu.current_thread().unwrap();
            let ctn_ptr = cpu.owning_container();
            assert({
                &&& krnl.prc_mp.dom().contains(prc_ptr)
                &&& krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr
                &&& krnl.ctn_mp.dom().contains(ctn_ptr)
                &&& krnl.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().contains(prc_ptr)
                &&& krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().container_depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
                &&& krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
            }) by {
                process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr);
                container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
            };

            let process_res = krnl.wlock_process_unless_killed(prc_ptr, Ghost(cpu_id), Tracked(lctx));
            if process_res.is_none() {
                krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(prc_ptr), None, None, None, None);
                    alloc_thread_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                    alloc_thread_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.unwrap();

            assert({
                &&& krnl.thrd_mp.dom().contains(thrd_ptr)
                &&& krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr
                &&& krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr
                &&& krnl.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().contains(thrd_ptr)
                &&& krnl.prc_mp.spec_index(prc_ptr).view().state.view() is Running
                &&& krnl.thrd_mp.spec_index(thrd_ptr).view().container_depth == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().container_depth
                &&& krnl.thrd_mp.spec_index(thrd_ptr).view().process_depth == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().depth
            }) by {
                thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr);
                process_perms_wf_at(krnl.prc_mp, prc_ptr);
            };
            let thread_res = krnl.wlock_current_running_thread_unless_killed(thrd_ptr, Tracked(lctx));
            if thread_res.is_none() {
                krnl.wunlock_process(prc_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(prc_ptr), Some(thrd_ptr), None, None, None);
                    alloc_thread_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorThreadKilled);
                    alloc_thread_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorThreadKilled);
                }
                return RetValueType::ErrorThreadKilled;
            }
            let Tracked(thread_lock_perm) = thread_res.unwrap();

            let process_quota_1g = krnl.prc_mp.borrow_typed(prc_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm)).quota_1g;
            if process_quota_1g < alloc_amount {
                krnl.wunlock_thread(thrd_ptr, Tracked(lctx), Tracked(thread_lock_perm));
                krnl.wunlock_process(prc_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(prc_ptr), Some(thrd_ptr), None, None, None);
                    alloc_thread_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorNoQuota);
                    alloc_thread_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorNoQuota);
                }
                return RetValueType::ErrorNoQuota;
            }

            let thread_quota_1g = krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm)).quota_1g;
            if alloc_amount > usize::MAX - thread_quota_1g {
                krnl.wunlock_thread(thrd_ptr, Tracked(lctx), Tracked(thread_lock_perm));
                krnl.wunlock_process(prc_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(prc_ptr), Some(thrd_ptr), None, None, None);
                    alloc_thread_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorThreadQuotaOverflow);
                    alloc_thread_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::ErrorThreadQuotaOverflow);
                }
                return RetValueType::ErrorThreadQuotaOverflow;
            }

            proof { alloc_thread_quota_1g_result_from_k(&*old(krnl), cpu_id, alloc_amount, RetValueType::Success); }
            if alloc_amount == 0 {
                krnl.wunlock_thread(thrd_ptr, Tracked(lctx), Tracked(thread_lock_perm));
                krnl.wunlock_process(prc_ptr, Tracked(lctx), Tracked(process_lock_perm));
                krnl.wunlock_own_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                    steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(prc_ptr), Some(thrd_ptr), None, None, None);
                    alloc_thread_quota_1g_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::Success);
                }
                return RetValueType::Success;
            }
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            commit_alloc_thread_quota_1g(krnl, Tracked(lctx), Tracked(&mut *steps), cpu_id, ctn_ptr, prc_ptr, thrd_ptr, alloc_amount, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm));
            assert(krnl.all_objects_unlocked(lctx)) by { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); };
            return RetValueType::Success;
        }
}
