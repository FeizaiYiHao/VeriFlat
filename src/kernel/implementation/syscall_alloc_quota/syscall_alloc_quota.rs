use vstd::prelude::*;
use crate::*;
use super::syscall_alloc_quota_helpers::commit_alloc_quota_4k;
use super::syscall_alloc_quota_spec::*;
use super::syscall_alloc_quota_trace::*;

verus! {
        pub fn syscall_alloc_quota_4k(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(krnl).inv(),
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
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

            assert(
                {   &&& krnl.ctn_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container)
                    &&& krnl.ctn_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container).view_ghost().owned_processes.view()
                        .contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap())
                    &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some
                    &&& krnl.prc_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap())
                    &&& krnl.prc_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap()).view_rodata().view().owning_container
                        == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container
                }
            ) by { reveal(cpu_array_wf); reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(container_process_wf); };

            let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(lctx));
            let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process().unwrap();
            let container_ptr = cpu.owning_container();
            let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(lctx));
            if container_res.is_none() {
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                    steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                    alloc_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorContainerKilled);
                    assert(alloc_quota_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount) is ErrorContainerKilled) by {
                        kernel_cpu_projection_at(&*old(krnl), cpu_id); kernel_container_projection_at(&*old(krnl), container_ptr);
                    };
                }
                return RetValueType::ErrorContainerKilled;
            }
            let Tracked(container_lock_perm) = container_res.unwrap();
            let container_ro = krnl.ctn_mp.borrow_rodata(container_ptr);
            let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
            assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k) && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).wf()) by { reveal(allocator_perms_wf); reveal(container_allocator_wf); };

            let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(lctx));
            if process_res.is_none() {
                krnl.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                krnl.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                    steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                    alloc_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::ErrorProcessKilled);
                    assert(alloc_quota_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount) is ErrorProcessKilled) by {
                        kernel_cpu_projection_at(&*old(krnl), cpu_id); kernel_container_projection_at(&*old(krnl), container_ptr); kernel_process_projection_at(&*old(krnl), process_ptr);
                    };
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.unwrap();
            proof { assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0) by { reveal(thread_cpu_wf); reveal(process_thread_wf); }; }

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
                    assert(alloc_quota_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount) is ErrorContainerQuotaInsufficient) by {
                        kernel_cpu_projection_at(&*old(krnl), cpu_id); kernel_container_projection_at(&*old(krnl), container_ptr); kernel_process_projection_at(&*old(krnl), process_ptr);
                    };
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
                    assert(alloc_quota_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount) is ErrorProcessQuotaOverflow) by {
                        kernel_cpu_projection_at(&*old(krnl), cpu_id); kernel_container_projection_at(&*old(krnl), container_ptr); kernel_process_projection_at(&*old(krnl), process_ptr);
                    };
                }
                return RetValueType::ErrorProcessQuotaOverflow;
            }

            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(alloc_quota_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount) is Success) by {
                    kernel_cpu_projection_at(&*old(krnl), cpu_id); kernel_container_projection_at(&*old(krnl), container_ptr); kernel_process_projection_at(&*old(krnl), process_ptr);
                };
            }
            commit_alloc_quota_4k(krnl, Tracked(lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, alloc_ptr_4k, alloc_amount, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(quota_lock_perm), Tracked(process_lock_perm));
            assert(krnl.all_objects_unlocked(lctx)) by { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); };
            proof {
                if alloc_amount == 0 { alloc_quota_4k_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, alloc_amount, RetValueType::Success); }
            }
            return RetValueType::Success;
        }
}
