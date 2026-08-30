use vstd::prelude::*;
use vstd::assert_sets_equal;

use crate::*;

use super::mmap_4k_map_range::mmap_4k_build_and_map_leaf_range;
use super::mmap_4k_precheck::{mmap_4k_precheck, Mmap4kPrecheck};
use super::syscall_mmap_4k_spec::mmap_4k_syscall_range_mapped;

verus! {

    /// Map writable, executable anonymous 4K pages into the running
    /// process. Directory construction is kernel-only; every published leaf
    /// is one user-visible kernel step.
    pub fn syscall_mmap_4k(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        va: VAddr,
        range: usize,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(kernel).inv(),
            old(kernel).cpu_array.spec_index(cpu_id).view().view().state
                == CpuState::Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(kernel).all_objects_unlocked(old(lctx)),
            typed_lock_maps_aligned(old(kernel), old(lctx)),
            old(steps).steps.len() == 0,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
        ensures
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(kernel).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(kernel), final(lctx)),
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
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
                let process_ptr = old(kernel).cpu_array.spec_index(cpu_id)
                    .view().view().current_process->Some_0;
                let pagetable_ptr = old(kernel).process_map.spec_index(process_ptr)
                    .view().pagetable;
                &&& range > 0
                &&& va_4k_valid(va)
                &&& final(kernel).pagetable_map.dom().contains(pagetable_ptr)
                &&& mmap_4k_syscall_range_mapped(
                    final(kernel).pagetable_map.spec_index(pagetable_ptr).view(),
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
                enter_kernel_view_release_preserving_typed_lock_alignment(
                    &*kernel, &mut *lctx,
                );
                steps.end_kernel_step(&*kernel, &*lctx);
            }
            return RetValueType::Error;
        }

        let span = range * 4096usize;
        if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
            proof {
                enter_kernel_view_release_preserving_typed_lock_alignment(
                    &*kernel, &mut *lctx,
                );
                steps.end_kernel_step(&*kernel, &*lctx);
            }
            return RetValueType::Error;
        }
        let va_range = VaRange4K::new(va, range);

        assert({
            let cpu = kernel.cpu_array.spec_index(cpu_id).view().view();
            &&& cpu.current_process is Some
            &&& cpu.current_thread is Some
            &&& kernel.container_map.dom().contains(cpu.owning_container)
            &&& kernel.process_map.dom().contains(cpu.current_process.unwrap())
            &&& kernel.thread_map.dom().contains(cpu.current_thread.unwrap())
            &&& kernel.thread_map.spec_index(cpu.current_thread.unwrap()).view()
                .owning_proc == cpu.current_process.unwrap()
            &&& kernel.thread_map.spec_index(cpu.current_thread.unwrap()).view()
                .owning_container == cpu.owning_container
            &&& kernel.thread_map.spec_index(cpu.current_thread.unwrap()).view()
                .state == (ThreadState::RUNNING { cpu_id })
            &&& mmap_4k_no_page_locks(&*lctx)
        }) by {
            reveal(container_cpu_wf);
            reveal(process_cpu_wf);
            reveal(thread_cpu_wf);
            reveal(process_thread_wf);
            reveal(container_thread_wf);
        };

        let Tracked(cpu_lock_perm) = kernel.wlock_cpu(
            cpu_id,
            Tracked(&mut *lctx),
        );
        let cpu = kernel.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
        let process_ptr = cpu.current_process.unwrap();
        let thread_ptr = cpu.current_thread.unwrap();
        let container_ptr = cpu.owning_container;

        assert(lctx.lock_id_acyclic(
            kernel.container_map.lock_id_by_key(container_ptr),
        )) by {
            reveal(typed_lock_maps_aligned);
            reveal(container_cpu_wf);
        };
        let container_res = kernel.wlock_container_unless_killed(
            container_ptr,
            Tracked(&mut *lctx),
        );
        if let (false, _) = container_res {
            kernel.wunlock_cpu(
                cpu_id,
                Tracked(&mut *lctx),
                Tracked(cpu_lock_perm),
            );
            proof {
                steps.end_kernel_step(&*kernel, &*lctx);
            }
            return RetValueType::ErrorContainerKilled;
        }
        let Tracked(container_lock_perm) = container_res.1.unwrap();

        assert(lctx.lock_id_acyclic(
            kernel.process_map.lock_id_by_key(process_ptr),
        )) by {
            reveal(typed_lock_maps_aligned);
            reveal(container_process_wf);
            reveal(process_cpu_wf);
        };
        let process_res = kernel.wlock_process_unless_killed(
            process_ptr,
            Tracked(&mut *lctx),
        );
        if let (false, _) = process_res {
            kernel.wunlock_container(
                container_ptr,
                Tracked(&mut *lctx),
                Tracked(container_lock_perm),
            );
            kernel.wunlock_cpu(
                cpu_id,
                Tracked(&mut *lctx),
                Tracked(cpu_lock_perm),
            );
            proof {
                steps.end_kernel_step(&*kernel, &*lctx);
            }
            return RetValueType::ErrorProcessKilled;
        }
        let Tracked(process_lock_perm) = process_res.1.unwrap();

        assert(lctx.lock_id_acyclic(
            kernel.thread_map.lock_id_by_key(thread_ptr),
        )) by {
            reveal(typed_lock_maps_aligned);
            reveal(process_thread_wf);
            reveal(process_perms_wf);
            reveal(thread_perms_wf);
        };
        let thread_res = kernel.wlock_thread_unless_killed(
            thread_ptr,
            Tracked(&mut *lctx),
        );
        if let (false, _) = thread_res {
            kernel.wunlock_process(
                process_ptr,
                Tracked(&mut *lctx),
                Tracked(process_lock_perm),
            );
            kernel.wunlock_container(
                container_ptr,
                Tracked(&mut *lctx),
                Tracked(container_lock_perm),
            );
            kernel.wunlock_cpu(
                cpu_id,
                Tracked(&mut *lctx),
                Tracked(cpu_lock_perm),
            );
            proof {
                steps.end_kernel_step(&*kernel, &*lctx);
            }
            return RetValueType::ErrorThreadKilled;
        }
        let Tracked(thread_lock_perm) = thread_res.1.unwrap();

        let container_ro = kernel.container_map.borrow_rodata(container_ptr);
        let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
        let thread = kernel.thread_map.borrow(
            thread_ptr,
            Tracked(&thread_lock_perm),
        );
        let pagetable_ptr = thread.proc_pagetable_ptr;
        assert({
            &&& kernel.allocator_4k_map.dom().contains(alloc_ptr_4k)
            &&& kernel.pagetable_map.dom().contains(pagetable_ptr)
            &&& kernel.thread_map.spec_index(thread_ptr).view().owning_proc
                == process_ptr
            &&& kernel.thread_map.spec_index(thread_ptr).view().owning_container
                == container_ptr
            &&& kernel.process_map.spec_index(process_ptr).view_rodata().view()
                .owning_container == container_ptr
            &&& kernel.process_map.spec_index(process_ptr).view().pagetable
                == pagetable_ptr
            &&& !kernel.pagetable_map.spec_index(pagetable_ptr)
                .locked_by_thread(lctx.thread_id())
            &&& mmap_4k_no_page_locks(&*lctx)
        }) by {
            reveal(allocator_perms_wf);
            reveal(container_allocator_wf);
            reveal(process_thread_wf);
            reveal(process_pagetable_match);
        };

        assert(lctx.lock_id_acyclic(
            kernel.pagetable_map.lock_id_by_key(pagetable_ptr),
        )) by {
            reveal(thread_cpu_wf);
            reveal(thread_perms_wf);
            reveal(typed_lock_maps_aligned);
            reveal(pagetable_perms_wf);
        };
        let Tracked(pagetable_lock_perm) = kernel.wlock_pagetable(
            pagetable_ptr,
            Tracked(&mut *lctx),
        );
        proof {
        let result;
        match precheck {
            Mmap4kPrecheck::Ready => {
                assert(
                    kernel.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                        <= spec_v2l4index(va_range.start)
                ) by {
                    assert(spec_va2index(va_range.start).0
                        == spec_v2l4index(va_range.start)) by (bit_vector);
                };
                let build = mmap_4k_build_and_map_leaf_range(kernel,
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
                                kernel.pagetable_map.spec_index(pagetable_ptr).view(),
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

        kernel.wunlock_pagetable(
            pagetable_ptr,
            Tracked(&mut *lctx),
            Tracked(pagetable_lock_perm),
        );
        kernel.wunlock_thread(
            thread_ptr,
            Tracked(&mut *lctx),
            Tracked(thread_lock_perm),
        );
        kernel.wunlock_process(
            process_ptr,
            Tracked(&mut *lctx),
            Tracked(process_lock_perm),
        );
        kernel.wunlock_container(
            container_ptr,
            Tracked(&mut *lctx),
            Tracked(container_lock_perm),
        );
        kernel.wunlock_cpu(
            cpu_id,
            Tracked(&mut *lctx),
            Tracked(cpu_lock_perm),
        );
        proof {
            assert_sets_equal!(
                lctx.no_locks_held(), held_lock => {}
            );
            assert(kernel.all_objects_unlocked(&*lctx)) by {
                reveal(pagetable_objects_unlocked_except);
                reveal(thread_objects_unlocked_except);
                reveal(process_objects_unlocked_except);
                reveal(container_objects_unlocked_except);
                reveal(cpu_objects_unlocked_except);
            };
            steps.end_kernel_step(&*kernel, &*lctx);
        }
        result
    }


} // verus!
