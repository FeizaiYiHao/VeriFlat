use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;
use super::syscall_alloc_quota_helpers::kernel_u_only_process_quota_4k_changed;

verus! {
    impl KernelK{
        pub fn syscall_alloc_quota_4k(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(self).inv(),
                old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                old(self).all_objects_unlocked(old(lctx)),
                old(steps).steps.len() == 0,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(steps).steps.len() <= 1,
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
                final(self).all_objects_unlocked(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
                final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                ret is Success
                    || ret is ErrorContainerKilled
                    || ret is ErrorContainerQuotaInsufficient
                    || ret is ErrorProcessKilled
                    || ret is ErrorProcessQuotaOverflow,
                !(ret is Success) ==> final(steps).steps.len() == 0,
                ret is Success && alloc_amount == 0 ==> final(steps).steps.len() == 0,
                ret is Success && alloc_amount > 0 ==> {
                    let process_ptr = old(self).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0;
                    &&& final(steps).steps.len() == 1
                    &&& final(steps).steps.last().old_u == kernel_k_to_kernel_u(*old(self))
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
                    self.container_map.dom().contains(self.cpu_array.spec_index(cpu_id).view().view().owning_container)
                    &&&
                    self.container_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().owning_container).view().owned_processes.view()
                        .contains(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap())
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().current_process is Some
                    &&&
                    self.process_map.dom().contains(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap())
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().process_depth == self.process_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap()).view_rodata().view().depth
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().container_depth == self.container_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().owning_container).view_rodata().view().depth
                    &&&
                    self.process_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap()).view_rodata().view().container_depth
                        ==
                        self.container_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().owning_container).view_rodata().view().depth
                }
            ) by {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(process_perms_wf);
                reveal(container_cpu_wf);
                reveal(process_cpu_wf);
                reveal(container_process_wf);
            };

            let Tracked(cpu_lock_perm) = self.wlock_cpu(cpu_id, Tracked(lctx));
            let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process.unwrap();
            let container_ptr = cpu.owning_container;
            let container_res = self.wlock_container_unless_killed(container_ptr, Tracked(lctx));
            if let (false, _) = container_res{
                self.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                        kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    };
                    steps.end_kernel_step(&*self, &*lctx);
                }
                return RetValueType::ErrorContainerKilled;
            }
            let Tracked(container_lock_perm) = container_res.1.unwrap();
            let container_ro = self.container_map.borrow_rodata(container_ptr);
            let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
            assert(
                {
                    &&&
                    self.allocator_4k_map.dom().contains(alloc_ptr_4k)
                    &&&
                    self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                    &&&
                    self.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().container_depth
                        == self.container_map.spec_index(container_ptr).view_rodata().view().depth
                }
            ) by {
                reveal(allocator_perms_wf);
                reveal(container_allocator_wf);
            };

            let Tracked(quota_lock_perm) = self.wlock_quota_4k(alloc_ptr_4k, Tracked(lctx));

            let quota_ref = self.allocator_4k_map.borrow_quota(
                alloc_ptr_4k, Tracked(&quota_lock_perm),
            );
            if quota_ref.value < alloc_amount {
                self.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                self.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                self.wunlock_quota_4k(alloc_ptr_4k, Tracked(lctx), Tracked(quota_lock_perm));
                proof {
                    assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                        kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    };
                    steps.end_kernel_step(&*self, &*lctx);
                }
                return RetValueType::ErrorContainerQuotaInsufficient;
            }

            let process_res = self.wlock_process_unless_killed(process_ptr, Tracked(lctx));
            if let (false, _) = process_res {
                self.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                self.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                self.wunlock_quota_4k(alloc_ptr_4k, Tracked(lctx), Tracked(quota_lock_perm));
                proof {
                    assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                        kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    };
                    steps.end_kernel_step(&*self, &*lctx);
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.1.unwrap();
            let process_ref: &Process = self.process_map.borrow(process_ptr, Tracked(&process_lock_perm));
            let process_quota_4k = process_ref.quota_4k;
            if alloc_amount > usize::MAX - process_quota_4k {
                self.wunlock_cpu(cpu_id, Tracked(lctx), Tracked(cpu_lock_perm));
                self.wunlock_container(container_ptr, Tracked(lctx), Tracked(container_lock_perm));
                self.wunlock_quota_4k(alloc_ptr_4k, Tracked(lctx), Tracked(quota_lock_perm));
                self.wunlock_process(process_ptr, Tracked(lctx), Tracked(process_lock_perm));
                proof {
                    assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                        kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                    };
                    steps.end_kernel_step(&*self, &*lctx);
                }
                return RetValueType::ErrorProcessQuotaOverflow;
            }

            proof {
                assert(steps.snap_shot == kernel_k_to_kernel_u(*self)) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
            self.commit_alloc_quota_4k(
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

}
