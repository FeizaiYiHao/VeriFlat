use vstd::prelude::*;
use vstd::assert_sets_equal;

use crate::*;

use super::mmap_4k_build_structure::Mmap4kStructureBuild;
use super::mmap_4k_context::{
    mmap_4k_allocation_ready,
    mmap_4k_held_context,
    mmap_4k_no_page_locks,
};
use super::mmap_4k_precheck::Mmap4kPrecheck;
use super::syscall_mmap_4k_spec::mmap_4k_syscall_range_mapped;

verus! {
impl KernelK {
    /// Map writable, executable anonymous 4K pages into the running
    /// process. Directory construction is kernel-only; every published leaf
    /// is one user-visible kernel step.
    pub fn syscall_mmap_4k(
        &mut self,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        va: VAddr,
        range: usize,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(self).inv(),
            old(self).cpu_array.spec_index(cpu_id).view().view().state
                == CpuState::Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            old(self).all_objects_unlocked(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(steps).steps.len() == 0,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
        ensures
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(self).all_objects_unlocked(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            ret is Success
                || ret is Error
                || ret is ErrorVaInUse
                || ret is ErrorNoQuota
                || ret is ErrorContainerKilled
                || ret is ErrorProcessKilled
                || ret is ErrorThreadKilled,
            ret is Success ==> final(steps).steps.len() == range,
            !(ret is Success) ==> final(steps).steps.len() == 0,
            ret is Success ==> {
                let process_ptr = old(self).cpu_array.spec_index(cpu_id)
                    .view().view().current_process->Some_0;
                let pagetable_ptr = old(self).process_map.spec_index(process_ptr)
                    .view().pagetable;
                &&& range > 0
                &&& va_4k_valid(va)
                &&& final(self).pagetable_map.dom().contains(pagetable_ptr)
                &&& mmap_4k_syscall_range_mapped(
                    final(self).pagetable_map.spec_index(pagetable_ptr).view(),
                    va,
                    range,
                )
            },
    {
        if range == 0
            || range > usize::MAX / 4096usize
            || range > usize::MAX / 4usize
            || !va_4k_valid(va)
        {
            proof {
                enter_kernel_view_release_preserving_lock_id_alignment(
                    &*self, &mut *lctx,
                );
                steps.end_kernel_step(&*self, &*lctx);
            }
            return RetValueType::Error;
        }

        let span = range * 4096usize;
        if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
            proof {
                enter_kernel_view_release_preserving_lock_id_alignment(
                    &*self, &mut *lctx,
                );
                steps.end_kernel_step(&*self, &*lctx);
            }
            return RetValueType::Error;
        }
        let va_range = VaRange4K::new(va, range);

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
            &&& mmap_4k_no_page_locks(&*lctx)
        }) by {
            reveal(container_cpu_wf);
            reveal(process_cpu_wf);
            reveal(thread_cpu_wf);
            reveal(process_thread_wf);
            reveal(container_thread_wf);
        };

        let Tracked(cpu_lock_perm) = self.wlock_cpu(
            cpu_id,
            Tracked(&mut *lctx),
        );
        let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
        let process_ptr = cpu.current_process.unwrap();
        let thread_ptr = cpu.current_thread.unwrap();
        let container_ptr = cpu.owning_container;

        assert(lctx.lock_id_acyclic(
            self.container_map.lock_id_by_key(container_ptr),
        )) by {
            reveal(lock_id_aligned);
            reveal(container_cpu_wf);
        };
        let container_res = self.wlock_container_unless_killed(
            container_ptr,
            Tracked(&mut *lctx),
        );
        if let (false, _) = container_res {
            self.wunlock_cpu(
                cpu_id,
                Tracked(&mut *lctx),
                Tracked(cpu_lock_perm),
            );
            proof {
                steps.end_kernel_step(&*self, &*lctx);
            }
            return RetValueType::ErrorContainerKilled;
        }
        let Tracked(container_lock_perm) = container_res.1.unwrap();

        assert(lctx.lock_id_acyclic(
            self.process_map.lock_id_by_key(process_ptr),
        )) by {
            reveal(lock_id_aligned);
            reveal(container_process_wf);
            reveal(process_cpu_wf);
        };
        let process_res = self.wlock_process_unless_killed(
            process_ptr,
            Tracked(&mut *lctx),
        );
        if let (false, _) = process_res {
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
                steps.end_kernel_step(&*self, &*lctx);
            }
            return RetValueType::ErrorProcessKilled;
        }
        let Tracked(process_lock_perm) = process_res.1.unwrap();

        assert(lctx.lock_id_acyclic(
            self.thread_map.lock_id_by_key(thread_ptr),
        )) by {
            reveal(lock_id_aligned);
            reveal(process_thread_wf);
            reveal(process_perms_wf);
            reveal(thread_perms_wf);
        };
        let thread_res = self.wlock_thread_unless_killed(
            thread_ptr,
            Tracked(&mut *lctx),
        );
        if let (false, _) = thread_res {
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
                steps.end_kernel_step(&*self, &*lctx);
            }
            return RetValueType::ErrorThreadKilled;
        }
        let Tracked(thread_lock_perm) = thread_res.1.unwrap();

        let container_ro = self.container_map.borrow_rodata(container_ptr);
        let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
        let thread = self.thread_map.borrow(
            thread_ptr,
            Tracked(&thread_lock_perm),
        );
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
            &&& !self.pagetable_map.spec_index(pagetable_ptr)
                .locked_by_thread(lctx.thread_id())
            &&& mmap_4k_no_page_locks(&*lctx)
        }) by {
            reveal(allocator_perms_wf);
            reveal(container_allocator_wf);
            reveal(process_thread_wf);
            reveal(process_pagetable_match);
        };

        assert(lctx.lock_id_acyclic(
            self.pagetable_map.lock_id_by_key(pagetable_ptr),
        )) by {
            reveal(thread_cpu_wf);
            reveal(thread_perms_wf);
            reveal(lock_id_aligned);
            reveal(pagetable_perms_wf);
        };
        let Tracked(pagetable_lock_perm) = self.wlock_pagetable(
            pagetable_ptr,
            Tracked(&mut *lctx),
        );
        proof {
            assert_sets_equal!(lctx.lock_id_set() == set![
                (self.cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id)),
                (self.container_map.lock_id_by_key(container_ptr),
                    KernelObjId::Container(container_ptr)),
                (self.process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr)),
                (self.thread_map.lock_id_by_key(thread_ptr),
                    KernelObjId::Thread(thread_ptr)),
                (self.pagetable_map.lock_id_by_key(pagetable_ptr),
                    KernelObjId::PageTable(pagetable_ptr)),
            ], held_lock => {});
            assert(mmap_4k_held_context(
                self,
                &*lctx,
                alloc_ptr_4k,
                thread_ptr,
                process_ptr,
                container_ptr,
                cpu_id,
                pagetable_ptr,
                &thread_lock_perm,
                &pagetable_lock_perm,
            )) by {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(process_perms_wf);
                reveal(thread_perms_wf);
                reveal(pagetable_perms_wf);
                reveal(container_allocator_wf);
            };
            assert(mmap_4k_allocation_ready(self, &*lctx)) by {
                assert(thread_lock_perm.ordering_lock_id().major
                    == THREAD_LOCK_MAJOR) by {
                    reveal(thread_cpu_wf);
                    reveal(thread_perms_wf);
                };
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(process_perms_wf);
                reveal(thread_perms_wf);
                reveal(pagetable_perms_wf);
            };
        }

        let precheck = self.mmap_4k_precheck(
            &va_range,
            thread_ptr,
            pagetable_ptr,
            Tracked(&*lctx),
            Tracked(&thread_lock_perm),
            Tracked(&pagetable_lock_perm),
        );
        let result;
        match precheck {
            Mmap4kPrecheck::Ready => {
                assert(
                    self.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                        <= spec_v2l4index(va_range.start)
                ) by {
                    assert(spec_va2index(va_range.start).0
                        == spec_v2l4index(va_range.start)) by (bit_vector);
                };
                let build = self.mmap_4k_build_and_map_leaf_range(
                    &va_range,
                    alloc_ptr_4k,
                    thread_ptr,
                    process_ptr,
                    container_ptr,
                    cpu_id,
                    pagetable_ptr,
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    Tracked(&thread_lock_perm),
                    Tracked(&pagetable_lock_perm),
                );
                match build {
                    Mmap4kStructureBuild::Ready => {
                        proof {
                            assert(mmap_4k_syscall_range_mapped(
                                self.pagetable_map.spec_index(pagetable_ptr).view(),
                                va,
                                range,
                            )) by {
                                va_range.va_range_lemma();
                            };
                        }
                        result = RetValueType::Success;
                    },
                    Mmap4kStructureBuild::NoQuota => {
                        result = RetValueType::ErrorNoQuota;
                    },
                    Mmap4kStructureBuild::InUse => {
                        result = RetValueType::ErrorVaInUse;
                    },
                }
            },
            Mmap4kPrecheck::NoQuota => {
                result = RetValueType::ErrorNoQuota;
            },
            Mmap4kPrecheck::Invalid => {
                result = RetValueType::Error;
            },
            Mmap4kPrecheck::InUse => {
                result = RetValueType::ErrorVaInUse;
            },
        }

        self.wunlock_pagetable(
            pagetable_ptr,
            Tracked(&mut *lctx),
            Tracked(pagetable_lock_perm),
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
            assert_sets_equal!(
                lctx.lock_id_set() == Set::<HeldLock>::empty(), held_lock => {}
            );
            steps.end_kernel_step(&*self, &*lctx);
        }
        result
    }
}

} // verus!
