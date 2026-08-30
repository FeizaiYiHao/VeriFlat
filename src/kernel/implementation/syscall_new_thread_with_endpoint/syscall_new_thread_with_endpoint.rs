use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;
use super::super::syscall_new_thread::syscall_new_thread_helpers::kernel_u_new_thread_changed;
use super::syscall_new_thread_with_endpoint_helpers::add_new_thread_with_endpoint;

verus! {

    /// Create a thread whose endpoint descriptor 0 aliases descriptor
    /// `endpoint_index` of the thread currently running on `cpu_id`.
    #[verifier::spinoff_prover]
    pub fn syscall_new_thread_with_endpoint(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            edp_idx_valid(endpoint_index),
            old(kernel).inv(),
            old(kernel).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
            old(kernel).cpu_array.spec_index(cpu_id).view().view().current_process is Some,
            old(kernel).cpu_array.spec_index(cpu_id).view().view().current_thread is Some,
            old(kernel).process_map.dom().contains(
                old(kernel).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0,
            ),
            old(kernel).container_map.dom().contains(
                old(kernel).process_map.spec_index(
                    old(kernel).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0,
                ).view_rodata().view().owning_container,
            ),
            {
                let process_ptr = old(kernel).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0;
                let container_ptr = old(kernel).process_map.spec_index(process_ptr)
                    .view_rodata().view().owning_container;
                old(kernel).scheduler_map.dom().contains(
                    old(kernel).container_map.spec_index(container_ptr)
                        .view_rodata().view().scheduler,
                )
            },
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom().is_empty(),
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(steps).steps.len() == 0,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            typed_lock_maps_aligned(old(kernel), old(lctx)),
        ensures
            final(steps).steps.len() <= 1,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            typed_lock_maps_aligned(final(kernel), final(lctx)),
            final(lctx).no_locks_held(),
            final(lctx).page_lock_map().dom().is_empty(),
            final(lctx).cpu_lock_map().dom().is_empty(),
            final(lctx).container_lock_map().dom().is_empty(),
            final(lctx).process_lock_map().dom().is_empty(),
            final(lctx).thread_lock_map().dom().is_empty(),
            final(lctx).endpoint_lock_map().dom().is_empty(),
            final(lctx).scheduler_lock_map().dom().is_empty(),
            final(lctx).pcid_allocator_lock_map().dom().is_empty(),
            final(lctx).pagetable_lock_map().dom().is_empty(),
            final(lctx).iommu_table_lock_map().dom().is_empty(),
            final(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            final(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            !(ret is Success) ==> final(steps).steps.len() == 0,
            ret is Success ==> {
                let process_ptr = old(kernel).cpu_array.spec_index(cpu_id)
                    .view().view().current_process->Some_0;
                &&& final(steps).steps.len() == 1
                &&& final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(kernel))
                &&& kernel_u_new_thread_changed(
                    final(steps).steps.last().old_u,
                    final(steps).steps.last().new_u,
                    process_ptr,
                )
            },
            ret is Success
                || ret is ErrorProcessKilled
                || ret is ErrorThreadKilled
                || ret is ErrorNoQuota
                || ret is Error,
    {
        proof {
            assert(
                kernel.cpu_array.spec_index(cpu_id).view().view().current_process is Some
                && kernel.cpu_array.spec_index(cpu_id).view().view().current_thread is Some
                && kernel.thread_map.spec_index(
                    kernel.cpu_array.spec_index(cpu_id).view().view()
                        .current_thread->Some_0
                ).view().state == (ThreadState::RUNNING { cpu_id })
            ) by {
                reveal(cpu_array_wf);
                reveal(process_cpu_wf);
                reveal(thread_cpu_wf);
            };
        }
        assert(!lctx.cpu_lock_map().dom().contains(cpu_id)) by {
            vstd::set::lemma_set_empty(cpu_id);
        };
        let Tracked(cpu_lock_perm) = kernel.wlock_cpu(cpu_id, Tracked(&mut *lctx));
        let cpu = kernel.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
        let process_ptr = cpu.current_process.unwrap();
        let current_thread_ptr = cpu.current_thread.unwrap();

        proof {
            assert(kernel.process_map.dom().contains(process_ptr)) by { reveal(process_cpu_wf); };
            assert(kernel.process_map.perms_wf()) by { reveal(process_perms_wf); };
        }
        let container_ptr = kernel.process_map.borrow_rodata(process_ptr)
            .borrow().owning_container;
        proof {
            assert(kernel.container_map.dom().contains(container_ptr)) by { reveal(container_process_wf); };
            assert(kernel.container_map.perms_wf()) by { reveal(container_perms_wf); };
        }
        let scheduler_ptr = kernel.container_map.borrow_rodata(container_ptr)
            .borrow().scheduler;

        proof {
            assert(kernel.process_map.lock_id_by_key(process_ptr).major
                == PROCESS_LOCK_MAJOR) by { reveal(process_perms_wf); };
            assert(kernel.process_map.lock_id_by_key(process_ptr)
                .spec_gt(kernel.cpu_array.lock_id_by_index(cpu_id))) by {
                reveal(container_cpu_wf);
                reveal(process_cpu_wf);
                reveal(container_process_wf);
            };
        }
        let process_res = kernel.wlock_process_unless_killed(
            process_ptr, Tracked(&mut *lctx),
        );
        if let (false, _) = process_res {
            proof {
                assert(steps.snap_shot == kernel_k_to_kernel_u(*kernel)) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel); };
            }
            release_cpu_and_finish_syscall(kernel,
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
                Tracked(cpu_lock_perm),
            );
            return RetValueType::ErrorProcessKilled;
        }
        let Tracked(process_lock_perm) = process_res.1.unwrap();

        proof {
            assert({
                &&& kernel.thread_map.dom().contains(current_thread_ptr)
                &&& kernel.thread_map.spec_index(current_thread_ptr).view().owning_proc
                    == process_ptr
                &&& kernel.thread_map.spec_index(current_thread_ptr).view().owning_container
                    == container_ptr
                &&& kernel.thread_map.spec_index(current_thread_ptr).view().container_depth
                    == kernel.process_map.spec_index(process_ptr).view_rodata().view().container_depth
                &&& kernel.thread_map.spec_index(current_thread_ptr).view().process_depth
                    == kernel.process_map.spec_index(process_ptr).view_rodata().view().depth
            }) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
            assert(kernel.thread_map.lock_id_by_key(current_thread_ptr)
                .spec_gt(kernel.process_map.lock_id_by_key(process_ptr))) by { reveal(process_thread_wf); reveal(process_perms_wf); reveal(thread_perms_wf); };
        }
        let thread_res = kernel.wlock_thread_unless_killed(
            current_thread_ptr, Tracked(&mut *lctx),
        );
        if let (false, _) = thread_res {
            proof {
                assert(steps.snap_shot == kernel_k_to_kernel_u(*kernel)) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel); };
            }
            release_cpu_and_process_and_finish_syscall(kernel,
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
                process_ptr, Tracked(process_lock_perm), Tracked(cpu_lock_perm),
            );
            return RetValueType::ErrorThreadKilled;
        }
        let Tracked(current_thread_lock_perm) = thread_res.1.unwrap();

        proof {
            assert(steps.snap_shot == kernel_k_to_kernel_u(*kernel)) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel); };
        }

        let thread_ref = kernel.thread_map.borrow(
            current_thread_ptr, Tracked(&current_thread_lock_perm),
        );
        let endpoint_option = *thread_ref.endpoint_descriptors.get(endpoint_index);
        if let None = endpoint_option {
            proof {
                assert(steps.snap_shot == kernel_k_to_kernel_u(*kernel)) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel); };
            }
            release_cpu_and_process_and_thread_and_finish_syscall(kernel,
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
                process_ptr, current_thread_ptr, Tracked(current_thread_lock_perm),
                Tracked(process_lock_perm), Tracked(cpu_lock_perm),
            );
            return RetValueType::Error;
        }
        let endpoint_ptr = endpoint_option.unwrap();

        if thread_ref.quota_4k < 1 {
            proof {
                assert(steps.snap_shot == kernel_k_to_kernel_u(*kernel)) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel); };
            }
            release_cpu_and_process_and_thread_and_finish_syscall(kernel,
                Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
                process_ptr, current_thread_ptr, Tracked(current_thread_lock_perm),
                Tracked(process_lock_perm), Tracked(cpu_lock_perm),
            );
            return RetValueType::ErrorNoQuota;
        }

        proof {
            assert({
                &&& kernel.endpoint_map.dom().contains(endpoint_ptr)
                &&& kernel.container_map.dom().contains(
                    kernel.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                )
                &&& kernel.endpoint_map.spec_index(endpoint_ptr).view().owning_threads
                    .view().contains((current_thread_ptr, endpoint_index))
            }) by { reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); };
            assert(
                kernel.container_map.dom().contains(
                    kernel.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                )
                && {
                    ||| kernel.endpoint_map.spec_index(endpoint_ptr).view().owning_container
                        == container_ptr
                    ||| kernel.container_map.spec_index(
                            kernel.endpoint_map.spec_index(endpoint_ptr).view().owning_container,
                        ).view().subtree_set.view().contains(container_ptr)
                }
            ) by { reveal(container_endpoint_wf); reveal(container_thread_endpoint_wf); };
            assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel); };
        }
        proof {
            assert(current_thread_lock_perm.ordering_lock_id().major
                == THREAD_LOCK_MAJOR) by {
                reveal(thread_cpu_wf);
                reveal(thread_perms_wf);
            };
            assert(kernel.endpoint_map.lock_id_by_key(endpoint_ptr).major
                == ENDPOINT_LOCK_MAJOR) by {
                reveal(endpoint_perms_wf);
            };
            assert(lctx.lock_id_acyclic(
                kernel.endpoint_map.lock_id_by_key(endpoint_ptr),
            )) by {
                reveal(process_perms_wf);
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
            };
        }
        let Tracked(endpoint_lock_perm) = kernel.wlock_endpoint(
            endpoint_ptr, Tracked(&mut *lctx),
        );

        proof {
            assert(kernel.scheduler_map.dom().contains(scheduler_ptr)) by {
                reveal(container_scheduler_wf);
            };
            let scheduler_lock_id = kernel.scheduler_map.lock_id_by_key(scheduler_ptr);
            assert(scheduler_lock_id.major == SCHEDULER_LOCK_MAJOR) by {
                reveal(scheduler_perms_wf);
            };
            assert(lctx.lock_id_acyclic(scheduler_lock_id)) by {
                reveal(process_perms_wf);
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
                reveal(scheduler_perms_wf);
            };
        }
        let Tracked(scheduler_lock_perm) = kernel.wlock_scheduler(
            scheduler_ptr, Tracked(&mut *lctx),
        );

        proof {
            assert({
                &&& lctx.holds_no_typed_allocator_locks(PageSize::SZ2m)
                &&& lctx.holds_no_typed_allocator_locks(PageSize::SZ1g)
            }) by {
                reveal(LocalContext::no_locks_held);
                reveal(LocalContext::holds_no_typed_allocator_locks);
            };
        }
        add_new_thread_with_endpoint(
            kernel,
            Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr,
            current_thread_ptr, container_ptr, scheduler_ptr, endpoint_ptr,
            endpoint_index, Tracked(process_lock_perm),
            Tracked(current_thread_lock_perm), Tracked(cpu_lock_perm),
            Tracked(scheduler_lock_perm), Tracked(endpoint_lock_perm),
        );
        RetValueType::Success
    }

}
