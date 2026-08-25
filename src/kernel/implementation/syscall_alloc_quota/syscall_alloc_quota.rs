use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;
use super::syscall_alloc_quota_helpers::{
    commit_alloc_quota_4k,
    kernel_u_only_process_quota_4k_changed,
};

verus! {
        pub fn syscall_alloc_quota_4k(kernel: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(kernel).inv(),
                old(kernel).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                old(kernel).all_objects_unlocked(old(lctx)),
                old(steps).steps.len() == 0,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
                lock_id_aligned(old(kernel), old(lctx)),
            ensures
                final(steps).steps.len() <= 1,
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
                final(kernel).all_objects_unlocked(final(lctx)),
                lock_id_aligned(final(kernel), final(lctx)),
                final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                ret is Success
                    || ret is ErrorContainerKilled
                    || ret is ErrorContainerQuotaInsufficient
                    || ret is ErrorProcessKilled
                    || ret is ErrorProcessQuotaOverflow,
                !(ret is Success) ==> final(steps).steps.len() == 0,
                ret is Success && alloc_amount == 0 ==> final(steps).steps.len() == 0,
                ret is Success && alloc_amount > 0 ==> {
                    let process_ptr = old(kernel).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0;
                    &&& final(steps).steps.len() == 1
                    &&& final(steps).steps.last().old_u == kernel_k_to_kernel_u(*old(kernel))
                    &&& kernel_u_only_process_quota_4k_changed(
                            final(steps).steps.last().old_u,
                            final(steps).steps.last().new_u,
                            process_ptr,
                            alloc_amount as int,
                        )
                },
        {
            assert(
                {
                    &&&
                    kernel.container_map.dom().contains(kernel.cpu_array.spec_index(cpu_id).view().view().owning_container)
                    &&&
                    kernel.container_map.spec_index(kernel.cpu_array.spec_index(cpu_id).view().view().owning_container).view().owned_processes.view()
                        .contains(kernel.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap())
                    &&&
                    kernel.cpu_array.spec_index(cpu_id).view().view().current_process is Some
                    &&&
                    kernel.process_map.dom().contains(kernel.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap())
                    &&&
                    kernel.cpu_array.spec_index(cpu_id).view().view().process_depth == kernel.process_map.spec_index(kernel.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap()).view_rodata().view().depth
                    &&&
                    kernel.cpu_array.spec_index(cpu_id).view().view().container_depth == kernel.container_map.spec_index(kernel.cpu_array.spec_index(cpu_id).view().view().owning_container).view_rodata().view().depth
                    &&&
                    kernel.process_map.spec_index(kernel.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap()).view_rodata().view().container_depth
                        ==
                        kernel.container_map.spec_index(kernel.cpu_array.spec_index(cpu_id).view().view().owning_container).view_rodata().view().depth
                }
            ) by {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(process_perms_wf);
                reveal(container_cpu_wf);
                reveal(process_cpu_wf);
                reveal(container_process_wf);
            };

            let Tracked(cpu_lock_perm) = kernel.wlock_cpu(cpu_id, Tracked(lctx));
            let cpu = kernel.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process.unwrap();
            let container_ptr = cpu.owning_container;
            let container_res = kernel.wlock_container_unless_killed(container_ptr, Tracked(lctx));
            if let (false, _) = container_res{
                kernel.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                        kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
                    };
                    steps.end_kernel_step(&*kernel, &*lctx);
                }
                return RetValueType::ErrorContainerKilled;
            }
            let Tracked(container_lock_perm) = container_res.1.unwrap();
            let container_ro = kernel.container_map.borrow_rodata(container_ptr);
            let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
            assert(
                {
                    &&&
                    kernel.allocator_4k_map.dom().contains(alloc_ptr_4k)
                    &&&
                    kernel.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                    &&&
                    kernel.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().container_depth
                        == kernel.container_map.spec_index(container_ptr).view_rodata().view().depth
                }
            ) by {
                reveal(allocator_perms_wf);
                reveal(container_allocator_wf);
            };

            let Tracked(quota_lock_perm) = kernel.wlock_quota_4k(alloc_ptr_4k, Tracked(lctx));

            let quota_ref = kernel.allocator_4k_map.borrow_quota(
                alloc_ptr_4k, Tracked(&quota_lock_perm),
            );
            if quota_ref.value < alloc_amount {
                kernel.wunlock_quota_4k(alloc_ptr_4k, Tracked(lctx), Tracked(quota_lock_perm));
                kernel.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                kernel.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                        kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
                    };
                    steps.end_kernel_step(&*kernel, &*lctx);
                }
                return RetValueType::ErrorContainerQuotaInsufficient;
            }

            let process_res = kernel.wlock_process_unless_killed(process_ptr, Tracked(lctx));
            if let (false, _) = process_res {
                kernel.wunlock_quota_4k(alloc_ptr_4k, Tracked(lctx), Tracked(quota_lock_perm));
                kernel.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                kernel.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                        kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
                    };
                    steps.end_kernel_step(&*kernel, &*lctx);
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.1.unwrap();
            let process_ref: &Process = kernel.process_map.borrow(process_ptr, Tracked(&process_lock_perm));
            let process_quota_4k = process_ref.quota_4k;
            if alloc_amount > usize::MAX - process_quota_4k {
                kernel.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                kernel.wunlock_quota_4k(alloc_ptr_4k, Tracked(lctx), Tracked(quota_lock_perm));
                kernel.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                kernel.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_k_to_kernel_u(*kernel) == kernel_k_to_kernel_u(*old(kernel))) by {
                        kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
                    };
                    steps.end_kernel_step(&*kernel, &*lctx);
                }
                return RetValueType::ErrorProcessQuotaOverflow;
            }

            proof {
                assert(steps.snap_shot == kernel_k_to_kernel_u(*kernel)) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(kernel), kernel);
                };
            }
            commit_alloc_quota_4k(kernel,
                Tracked(lctx),
                Tracked(&mut *steps),
                cpu_id,
                container_ptr,
                process_ptr,
                alloc_ptr_4k,
                alloc_amount,
                Tracked(cpu_lock_perm),
                Tracked(container_lock_perm),
                Tracked(quota_lock_perm),
                Tracked(process_lock_perm),
            );
            return  RetValueType::Success;
        }
}
