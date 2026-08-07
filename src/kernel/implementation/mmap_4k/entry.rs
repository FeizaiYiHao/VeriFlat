use vstd::prelude::*;
use vstd::assert_sets_equal;

use crate::*;

use super::syscall_def::{Mmap4kRangeCheck, mmap_4k_raw_range_mapped};

verus! {

impl KernelK {
    /// Map `range` writable, non-executable anonymous 4K pages starting at
    /// `va`.  The syscall reserves the conservative upper bound of four pages
    /// per VA from the running process, then refunds every unused directory
    /// page in the final mapping step.
    pub fn syscall_mmap_4k(
        &mut self,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        va: VAddr,
        range: usize,
    ) -> (ret: RetValueType)
        requires
            cpu_id_valid(cpu_id),
            old(self).inv(),
            old(self).cpu_array.spec_index(cpu_id).view().view().state
                == CpuState::Running,
            old(lctx).wf(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).user_view_locking_state() is Acquire,
            old(lctx).lock_id_set() =~= Set::<LockId>::empty(),
            old(self).all_objects_unlocked(old(lctx)),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(steps).steps.len() == 0,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
        ensures
            final(self).inv(),
            final(lctx).wf(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() is Acquire,
            final(lctx).lock_id_set() =~= Set::<LockId>::empty(),
            final(self).all_objects_unlocked(final(lctx)),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            ret is Success
                || ret is Error
                || ret is ErrorVaInUse
                || ret is ErrorNoQuota
                || ret is ErrorContainerKilled
                || ret is ErrorProcessKilled
                || ret is ErrorThreadKilled,
            ret is Success ==> final(steps).steps.len() == range + 1,
            !(ret is Success) ==> final(steps).steps.len() == 1,
            final(steps).steps.len() > 0,
            final(steps).steps.last().new_k == *final(self),
            final(steps).steps.last().new_u
                == kernel_k_to_kernel_u(*final(self)),
            !(ret is Success) ==>
                final(steps).steps.last().old_u
                    == final(steps).steps.last().new_u,
            ret is Success ==> {
                let process_ptr = old(self).cpu_array.spec_index(cpu_id)
                    .view().view().current_process.unwrap();
                let pagetable_ptr = old(self).process_map.spec_index(process_ptr)
                    .view().pagetable;
                &&& range > 0
                &&& va_4k_valid(va)
                &&& final(self).pagetable_map.dom().contains(pagetable_ptr)
                &&& mmap_4k_raw_range_mapped(
                    final(self).pagetable_map.spec_index(pagetable_ptr).view(),
                    va,
                    range,
                    true,
                    true,
                )
            },
    {
        if range == 0
            || range > usize::MAX / 4096usize
            || range > usize::MAX / 4usize
            || !va_4k_valid(va)
        {
            proof {
                steps.begin_user_view_step(&*self, &mut *lctx);
                steps.end_user_view_step(&*self, &mut *lctx);
                assert(self.all_objects_unlocked(&*lctx)) by { self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx); };
            }
            return RetValueType::Error;
        }

        let span = range * 4096usize;
        if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
            proof {
                steps.begin_user_view_step(&*self, &mut *lctx);
                steps.end_user_view_step(&*self, &mut *lctx);
                assert(self.all_objects_unlocked(&*lctx)) by { self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx); };
            }
            return RetValueType::Error;
        }
        let va_range = VaRange4K::new(va, range);
        let credit = 4usize * range;

        assert({
            let cpu = self.cpu_array.spec_index(cpu_id).view().view();
            &&& cpu.current_process is Some
            &&& cpu.current_thread is Some
            &&& self.container_map.dom().contains(cpu.owning_container)
            &&& self.process_map.dom().contains(cpu.current_process.unwrap())
            &&& self.thread_map.dom().contains(cpu.current_thread.unwrap())
            &&& self.thread_map.spec_index(cpu.current_thread.unwrap()).view()
                .owning_proc == cpu.current_process.unwrap()
            &&& self.thread_map.spec_index(cpu.current_thread.unwrap()).view()
                .owning_container == cpu.owning_container
            &&& lctx.page_lock_map().dom()
                =~= Set::<PageIndex>::empty()
        }) by {
            reveal(LocalContext::wf);
            reveal(container_cpu_wf);
            reveal(process_cpu_wf);
            reveal(thread_cpu_wf);
            reveal(process_thread_wf);
            reveal(container_thread_wf);
        };

        let Tracked(cpu_lock_perm) = self.wlock_cpu(cpu_id, Tracked(&mut *lctx));
        let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
        let process_ptr = cpu.current_process.unwrap();
        let thread_ptr = cpu.current_thread.unwrap();
        let container_ptr = cpu.owning_container;

        assert(lctx.lock_id_acyclic(
            self.container_map.lock_id_by_key(container_ptr),
        )) by {
            reveal(cpu_locked_match_lctx);
            reveal(container_cpu_wf);
        };
        let container_res = self.wlock_container_unless_killed(
            container_ptr,
            Tracked(&mut *lctx),
        );
        if let (false, _) = container_res {
            proof {
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
                steps.begin_user_view_step(&*self, &mut *lctx);
            }
            self.wunlock_cpu(
                cpu_id,
                Tracked(&mut *lctx),
                Tracked(cpu_lock_perm),
            );
            proof {
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
                steps.end_user_view_step(&*self, &mut *lctx);
                assert(self.all_objects_unlocked(&*lctx)) by { self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx); };
            }
            return RetValueType::ErrorContainerKilled;
        }
        let Tracked(container_lock_perm) = container_res.1.unwrap();

        assert(lctx.lock_id_acyclic(
            self.process_map.lock_id_by_key(process_ptr),
        )) by {
            reveal(cpu_locked_match_lctx);
            reveal(container_locked_match_lctx);
            reveal(container_process_wf);
            reveal(process_cpu_wf);
        };
        let process_res = self.wlock_process_unless_killed(
            process_ptr,
            Tracked(&mut *lctx),
        );
        if let (false, _) = process_res {
            proof {
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
                steps.begin_user_view_step(&*self, &mut *lctx);
            }
            self.wunlock_container(
                container_ptr,
                Tracked(&mut *lctx),
                Tracked(container_lock_perm),
            );
            self.wunlock_cpu(
                cpu_id,
                Tracked(&mut *lctx),
                Tracked(cpu_lock_perm),
            );
            proof {
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
                steps.end_user_view_step(&*self, &mut *lctx);
                assert(self.all_objects_unlocked(&*lctx)) by { self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx); };
            }
            return RetValueType::ErrorProcessKilled;
        }
        let Tracked(process_lock_perm) = process_res.1.unwrap();

        assert(lctx.lock_id_acyclic(
            self.thread_map.lock_id_by_key(thread_ptr),
        )) by {
            reveal(cpu_locked_match_lctx);
            reveal(container_locked_match_lctx);
            reveal(process_locked_match_lctx);
            reveal(process_thread_wf);
            reveal(process_perms_wf);
            reveal(thread_perms_wf);
        };
        let thread_res = self.wlock_thread_unless_killed(
            thread_ptr,
            Tracked(&mut *lctx),
        );
        if let (false, _) = thread_res {
            proof {
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
                steps.begin_user_view_step(&*self, &mut *lctx);
            }
            self.wunlock_process(
                process_ptr,
                Tracked(&mut *lctx),
                Tracked(process_lock_perm),
            );
            self.wunlock_container(
                container_ptr,
                Tracked(&mut *lctx),
                Tracked(container_lock_perm),
            );
            self.wunlock_cpu(
                cpu_id,
                Tracked(&mut *lctx),
                Tracked(cpu_lock_perm),
            );
            proof {
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
                steps.end_user_view_step(&*self, &mut *lctx);
                assert(self.all_objects_unlocked(&*lctx)) by { self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx); };
            }
            return RetValueType::ErrorThreadKilled;
        }
        let Tracked(thread_lock_perm) = thread_res.1.unwrap();

        let container_ro = self.container_map.borrow_rodata(container_ptr);
        let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
        let thread = self.thread_map.borrow(thread_ptr, Tracked(&thread_lock_perm));
        let pagetable_ptr = thread.proc_pagetable_ptr;
        assert({
            &&& self.allocator_4k_map.dom().contains(alloc_ptr_4k)
            &&& self.pagetable_map.dom().contains(pagetable_ptr)
            &&& self.thread_map.spec_index(thread_ptr).view().owning_proc
                == process_ptr
            &&& self.thread_map.spec_index(thread_ptr).view().owning_container
                == container_ptr
            &&& self.process_map.spec_index(process_ptr).view_rodata().view()
                .owning_container == container_ptr
            &&& self.process_map.spec_index(process_ptr).view().pagetable
                == pagetable_ptr
            &&& lctx.page_lock_map().dom() =~= Set::<PageIndex>::empty()
        }) by {
            reveal(allocator_perms_wf);
            reveal(container_allocator_wf);
            reveal(process_thread_wf);
            reveal(process_pagetable_match);
        };

        let (Tracked(cache_perms), Tracked(global_pool_lock_perm)) =
            self.wlock_all_caches_and_global_pool(
                alloc_ptr_4k,
                Tracked(&mut *lctx),
            );
        let Tracked(pagetable_lock_perm) = self.wlock_pagetable(
            pagetable_ptr,
            Tracked(&mut *lctx),
        );
        assert({
            &&& lctx.page_lock_map().dom() =~= Set::<PageIndex>::empty()
            &&& lctx.lock_id_set() =~= set![
                self.cpu_array.lock_id_by_index(cpu_id),
                self.container_map.lock_id_by_key(container_ptr),
                self.process_map.lock_id_by_key(process_ptr),
                self.thread_map.lock_id_by_key(thread_ptr),
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id(),
                self.pagetable_map.lock_id_by_key(pagetable_ptr),
            ] + Self::allocator_cache_lock_id_prefix(NUM_CPUS)
        }) by {
            broadcast use vstd::set::group_set_lemmas;
            assert_sets_equal!(lctx.lock_id_set() == set![
                self.cpu_array.lock_id_by_index(cpu_id),
                self.container_map.lock_id_by_key(container_ptr),
                self.process_map.lock_id_by_key(process_ptr),
                self.thread_map.lock_id_by_key(thread_ptr),
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.lock_id(),
                self.pagetable_map.lock_id_by_key(pagetable_ptr),
                ] + Self::allocator_cache_lock_id_prefix(NUM_CPUS), lock_id => {});
                reveal(LocalContext::lock_maps_inserted);
        };

        let range_check = self.check_mmap_4k_range(
            &va_range,
            pagetable_ptr,
            Tracked(&*lctx),
            Tracked(&pagetable_lock_perm),
        );

        let mut error: Option<RetValueType> = None;
        let mut original_process_quota: usize = 0;
        let mut original_thread_quota: usize = 0;
        match range_check {
            Mmap4kRangeCheck::Invalid => {
                error = Some(RetValueType::Error);
            },
            Mmap4kRangeCheck::InUse => {
                error = Some(RetValueType::ErrorVaInUse);
            },
            Mmap4kRangeCheck::Empty => {
                let process = self.process_map.borrow(
                    process_ptr,
                    Tracked(&process_lock_perm),
                );
                original_process_quota = process.quota_4k;
                let thread = self.thread_map.borrow(
                    thread_ptr,
                    Tracked(&thread_lock_perm),
                );
                original_thread_quota = thread.quota_4k;
                if original_process_quota < credit
                    || credit > usize::MAX - original_thread_quota
                {
                    error = Some(RetValueType::ErrorNoQuota);
                }
            },
        }

        if let Some(error_ret) = error {
            proof {
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
                steps.begin_user_view_step(&*self, &mut *lctx);
            }
            self.wunlock_pagetable(
                pagetable_ptr,
                Tracked(&mut *lctx),
                Tracked(pagetable_lock_perm),
            );
            assert({
                &&& Self::cache_perms_match_lctx(
                    self.allocator_4k_map,
                    alloc_ptr_4k,
                    &*lctx,
                    &cache_perms,
                )
                &&& self.allocator_4k_map.dom().contains(alloc_ptr_4k)
                &&& self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx)
                &&& global_pool_lock_perm.lock_id()
                    == self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.locking_thread()->Write_lock_id
            }) by {
                reveal(KernelK::cache_perms_match_lctx);
                reveal(allocator_4k_locked_match_lctx);
            };
            self.wunlock_all_caches(
                alloc_ptr_4k,
                Tracked(&mut *lctx),
                Tracked(cache_perms),
            );
            self.wunlock_allocator_global_pool(
                alloc_ptr_4k,
                Tracked(&mut *lctx),
                Tracked(global_pool_lock_perm),
            );
            self.wunlock_thread(
                thread_ptr,
                Tracked(&mut *lctx),
                Tracked(thread_lock_perm),
            );
            self.wunlock_process(
                process_ptr,
                Tracked(&mut *lctx),
                Tracked(process_lock_perm),
            );
            self.wunlock_container(
                container_ptr,
                Tracked(&mut *lctx),
                Tracked(container_lock_perm),
            );
            self.wunlock_cpu(
                cpu_id,
                Tracked(&mut *lctx),
                Tracked(cpu_lock_perm),
            );
            proof {
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
                steps.end_user_view_step(&*self, &mut *lctx);
                assert(self.all_objects_unlocked(&*lctx)) by { self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx); };
            }
            return error_ret;
        }

        proof {
            assert(steps.snap_shot == kernel_k_to_kernel_u(*self)) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            steps.begin_user_view_step(&*self, &mut *lctx);
        }
        self.reserve_process_4k_quota_for_thread(
            process_ptr,
            thread_ptr,
            credit,
            Tracked(&mut *lctx),
            Tracked(&process_lock_perm),
            Tracked(&thread_lock_perm),
        );
        proof {
            steps.end_user_view_step(&*self, &mut *lctx);
            assert(Self::cache_perms_match_lctx(
                self.allocator_4k_map,
                alloc_ptr_4k,
                &*lctx,
                &cache_perms,
            )) by {
                reveal(KernelK::cache_perms_match_lctx);
                reveal(allocator_4k_locked_match_lctx);
            };
            assert({
                &&& self.allocator_4k_map.dom().contains(alloc_ptr_4k)
                &&& self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx)
                &&& global_pool_lock_perm.lock_id()
                    == self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.locking_thread()->Write_lock_id
            }) by { reveal(allocator_4k_locked_match_lctx); };
            self.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(Self::cache_perms_match_lctx(
                self.allocator_4k_map,
                alloc_ptr_4k,
                &*lctx,
                &cache_perms,
            )) by {
                reveal(KernelK::cache_perms_match_lctx);
                reveal(allocator_4k_locked_match_lctx);
            };
            assert({
                &&& self.allocator_4k_map.dom().contains(alloc_ptr_4k)
                &&& self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx)
                &&& global_pool_lock_perm.lock_id()
                    == self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.locking_thread()->Write_lock_id
            }) by { reveal(allocator_4k_locked_match_lctx); };
            assert({
                &&& self.pagetable_map.dom().contains(pagetable_ptr)
                &&& self.pagetable_map.spec_index(pagetable_ptr)
                    .wlocked_by(&*lctx)
                &&& pagetable_lock_perm.lock_id()
                    == self.pagetable_map.spec_index(pagetable_ptr)
                        .locking_thread()->Write_lock_id
            }) by { reveal(pagetable_locked_match_lctx); };
            assert(lctx.lock_id_set() =~= set![
                lctx.cpu_lock_map().spec_index(cpu_id),
                lctx.container_lock_map().spec_index(container_ptr),
                lctx.process_lock_map().spec_index(process_ptr),
                lctx.thread_lock_map().spec_index(thread_ptr),
                lctx.allocator_4k_lock_map().spec_index(
                    AllocatorLockObjId::GlobalPool(alloc_ptr_4k),
                ),
                lctx.pagetable_lock_map().spec_index(pagetable_ptr),
            ] + Self::allocator_cache_lock_id_prefix(NUM_CPUS)) by {
                broadcast use vstd::set::group_set_lemmas;
                reveal(LocalContext::wf);
                reveal(cpu_locked_match_lctx);
                reveal(container_locked_match_lctx);
                reveal(process_locked_match_lctx);
                reveal(thread_locked_match_lctx);
                reveal(pagetable_locked_match_lctx);
                reveal(allocator_4k_locked_match_lctx);
                assert_sets_equal!(lctx.lock_id_set() == set![
                    lctx.cpu_lock_map().spec_index(cpu_id),
                    lctx.container_lock_map().spec_index(container_ptr),
                    lctx.process_lock_map().spec_index(process_ptr),
                    lctx.thread_lock_map().spec_index(thread_ptr),
                    lctx.allocator_4k_lock_map().spec_index(
                        AllocatorLockObjId::GlobalPool(alloc_ptr_4k),
                    ),
                    lctx.pagetable_lock_map().spec_index(pagetable_ptr),
                ] + Self::allocator_cache_lock_id_prefix(NUM_CPUS), lock_id => {});
            };
            assert(lctx.page_lock_map().dom()
                =~= Set::<PageIndex>::empty()) by { reveal(LocalContext::wf); };
        }

        self.commit_mmap_4k_range(
            &va_range,
            credit,
            original_process_quota,
            original_thread_quota,
            alloc_ptr_4k,
            thread_ptr,
            process_ptr,
            container_ptr,
            cpu_id,
            pagetable_ptr,
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(cache_perms),
            Tracked(global_pool_lock_perm),
            Tracked(thread_lock_perm),
            Tracked(process_lock_perm),
            Tracked(container_lock_perm),
            Tracked(cpu_lock_perm),
            Tracked(pagetable_lock_perm),
        );
        proof {
            assert(self.all_objects_unlocked(&*lctx)) by { self.lock_id_set_empty_imply_all_objects_unlocked(&*lctx); };
        }
        RetValueType::Success
    }
}

} // verus!
