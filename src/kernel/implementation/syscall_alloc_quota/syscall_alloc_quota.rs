use vstd::prelude::*;
use crate::*;
use super::syscall_alloc_quota_helpers::{
    commit_alloc_quota_4k,
    kernel_u_only_process_quota_4k_changed,
};

verus! {
        pub fn syscall_alloc_quota_4k(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(krnl).inv(),
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).no_locks_held(),
                old(krnl).all_objects_unlocked(old(lctx)),
                old(steps).steps.len() == 0,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
                final(krnl).all_objects_unlocked(final(lctx)),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(lctx).no_locks_held(),
                ret is Success || ret is ErrorContainerKilled || ret is ErrorContainerQuotaInsufficient || ret is ErrorProcessKilled || ret is ErrorProcessQuotaOverflow,
                !(ret is Success) ==> final(steps).steps.len() == 0,
                ret is Success && alloc_amount == 0 ==> final(steps).steps.len() == 0,
                ret is Success && alloc_amount > 0 ==> 
                    { 
                        let process_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process->Some_0;
                        &&& final(steps).steps.len() == 1 
                        &&& final(steps).steps.last().old_u == kernel_k_to_kernel_u(*old(krnl)) 
                        &&& kernel_u_only_process_quota_4k_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, process_ptr, alloc_amount as int) 
                    },
        {
            assert(
                {   &&& krnl.ctn_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container)
                    &&& krnl.ctn_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container).view().owned_processes.view()
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
                    steps.end_kernel_step(&*krnl, &*lctx);
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
                    steps.end_kernel_step(&*krnl, &*lctx);
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
                    assert(steps.snap_shot == kernel_k_to_kernel_u(*krnl)) by {
                        kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl);
                    };
                    steps.end_kernel_step(&*krnl, &*lctx);
                    assert(steps.steps == old(steps).steps) by { reveal(record_user_view_change); };
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
                    assert(steps.snap_shot == kernel_k_to_kernel_u(*krnl)) by {
                        kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl);
                    };
                    steps.end_kernel_step(&*krnl, &*lctx);
                    assert(steps.steps == old(steps).steps) by { reveal(record_user_view_change); };
                }
                return RetValueType::ErrorProcessQuotaOverflow;
            }

            proof {
                assert(steps.snap_shot == kernel_k_to_kernel_u(*krnl)) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl);
                };
            }
            commit_alloc_quota_4k(krnl, Tracked(lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, alloc_ptr_4k, alloc_amount, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(quota_lock_perm), Tracked(process_lock_perm));
            assert(krnl.all_objects_unlocked(lctx)) by { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); };
            return  RetValueType::Success;
        }
}
