use vstd::prelude::*;

use crate::*;

use super::mmap_4k_map_range::mmap_4k_map_leaf_range;
use super::mmap_4k_precheck::{mmap_4k_precheck, Mmap4kPrecheck};
use super::syscall_mmap_4k_spec::*;
use super::syscall_mmap_4k_trace::*;

verus! {
    /// Map writable, executable anonymous 4K pages into the running process.
    /// Success records an entering step that write-locks the cpu, thread, and
    /// pagetable, one step per installed directory page or published leaf, and
    /// an exiting step that unlocks all three. Failure records no step. The result is
    /// `mmap_4k_syscall_result` of the state at entry.
    #[verifier::spinoff_prover]
    pub fn syscall_mmap_4k(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(krnl).all_objects_unlocked(old(lctx)),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(steps).nonlock_view().len() == 0,
            old(steps).view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            ret == mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range),
            ret is Success ==> range + 2 <= final(steps).nonlock_view().len() <= 4 * range + 2,
            !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
            !(ret is Success) ==> final(steps).view().len() == 0,
            ret is Success ==> mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range),
            ret is Success ==> mmap_4k_syscall_success_mapped(old(krnl), final(krnl), cpu_id, va, range),
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        if range == 0 || range > usize::MAX / 4096usize || !va_4k_valid(va)
        {
            proof {
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
                steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
            }
            return RetValueType::Error;
        }

        let span = range * 4096usize;
        if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
            proof {
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
                steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
            }
            return RetValueType::Error;
        }
        let va_range = VaRange4K::new(va, range);

        assert({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view();
            &&& cpu.current_process() is Some
            &&& cpu.current_thread() is Some
            &&& krnl.ctn_mp.dom().contains(cpu.owning_container())
            &&& krnl.prc_mp.dom().contains(cpu.current_process().unwrap())
            &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().owning_container == cpu.owning_container()
            &&& !krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view().zombie
            &&& krnl.thr_mp.dom().contains(cpu.current_thread().unwrap())
            &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view_ghost().owned_processes.view().contains(cpu.current_process().unwrap())
            &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_proc == cpu.current_process().unwrap()
            &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_container == cpu.owning_container()
            &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().state == (ThreadState::RUNNING { cpu_id })
        }) by { reveal(container_cpu_wf); reveal(container_process_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); reveal(process_thread_wf); reveal(container_thread_wf); };

        let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
        let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
        let process_ptr = cpu.current_process().unwrap();
        let thread_ptr = cpu.current_thread().unwrap();
        let container_ptr = cpu.owning_container();

        let thread_res = krnl.wlock_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
        if thread_res.is_none() {
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                assert(mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is ErrorThreadKilled) by { kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None); };
            }
            return RetValueType::ErrorThreadKilled;
        }
        let Tracked(thread_lock_perm) = thread_res.unwrap();

        assert(krnl.ctn_mp.view().spec_index(container_ptr).is_init() && krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr) by { container_perms_wf_at(krnl.ctn_mp, container_ptr); };
        let container_ro = krnl.ctn_mp.borrow_rodata(container_ptr);
        let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
        let thread = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
        let pagetable_ptr = thread.proc_pagetable_ptr;
        let quota_4k = thread.quota_4k;

        assert({
            &&& krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)
            &&& krnl.pt_mp.dom().contains(pagetable_ptr)
            &&& krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr
            &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr
        }) by { reveal(allocator_perms_wf); reveal(container_allocator_wf); reveal(process_thread_wf); reveal(process_pagetable_match); };

        let result = if quota_4k < 4 * range {
            proof { assert(mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is ErrorNoQuota) by { kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None); }; }
            RetValueType::ErrorNoQuota
        } else {
            let Tracked(pagetable_lock_perm) = krnl.wlock_pagetable(pagetable_ptr, Tracked(&mut *lctx));
            let precheck = mmap_4k_precheck(krnl, &va_range, pagetable_ptr, Tracked(&*lctx), Tracked(&pagetable_lock_perm));
            let result = match precheck {
                Mmap4kPrecheck::Ready => {
                    proof {
                        assert(mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is Success) by {
                            kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None); kernel_l4_end_projection_at(&*old(krnl), pagetable_ptr);
                            kernel_pagetable_mappings_projection_at(&*old(krnl), process_ptr);
                        };
                    }
                    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::Mmap4k { range: va_range, mapped: 0, directory: Mmap4kDirectory::None })), Tracked(&*lctx), Tracked(&thread_lock_perm));
                    proof {
                        use_type_invariant(&*steps);
                        let ghost entered_k = *krnl;
                        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
                        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
                        assert(mmap_4k_trace_after_enter(steps.view(), cpu_id, va_range)) by {
                            reveal(PageTable::spec_mapping_4k_va_range_empty); va_range.va_range_lemma();
                            kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(&*old(krnl), &entered_k, old(lctx), cpu_id, thread_ptr, process_ptr, pagetable_ptr);
                            kernel_l4_end_projection_at(&*old(krnl), pagetable_ptr);
                            kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None);
                            mmap_4k_enter_step_from_u(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id, process_ptr, thread_ptr, va_range);
                            mmap_4k_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id, va_range);
                        };
                        assert(krnl.ctn_mp.dom().contains(container_ptr) && krnl.prc_mp.dom().contains(process_ptr) && !krnl.prc_mp.spec_index(process_ptr).view().zombie) by { reveal(container_thread_wf); reveal(process_cpu_wf); };
                        assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)) by { reveal(container_allocator_wf); };
                    }
                    let ghost entered = steps.view();
                    mmap_4k_map_leaf_range(krnl, &va_range, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&thread_lock_perm), Tracked(&pagetable_lock_perm));
                    let ghost range_steps = steps.view();
                    let ghost exit_start = *krnl;
                    let ghost exit_lctx = *lctx;
                    proof {
                        assert(mmap_4k_trace_after_range(range_steps, cpu_id, va_range)) by { mmap_4k_trace_range_steps(&*steps, entered, cpu_id, va_range); };
                        assert(mmap_4k_syscall_range_mapped(krnl.pt_mp.spec_index(pagetable_ptr).view(), va, range)) by { va_range.va_range_lemma(); };
                    }
                    krnl.set_thread_syscall_progress(thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_lock_perm));
                    krnl.wunlock_pagetable(pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
                    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
                    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
                    proof {
                        assert(mmap_4k_exit_step_pre(kernel_k_to_kernel_u(exit_start), cpu_id)
                            && mmap_4k_exit_step(kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(*krnl), cpu_id)) by {
                            kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(&exit_start, &*krnl, &exit_lctx, cpu_id, thread_ptr, process_ptr, pagetable_ptr);
                            mmap_4k_exit_step_from_u(kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr);
                        };
                        use_type_invariant(&*steps);
                        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thread_ptr);
                        assert(mmap_4k_syscall_trace(steps.view(), cpu_id, va, range)) by {
                            va_range.va_range_lemma();
                            mmap_4k_trace_exit_step(&*steps, range_steps, kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(*krnl), cpu_id, va, range);
                        };
                    }
                    return RetValueType::Success;
                },
                Mmap4kPrecheck::Invalid => {
                    proof {
                        assert(mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is Error) by {
                            kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None); kernel_l4_end_projection_at(&*old(krnl), pagetable_ptr);
                        };
                    }
                    RetValueType::Error
                },
                Mmap4kPrecheck::InUse => {
                    proof {
                        assert(mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is ErrorVaInUse) by {
                            kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None); kernel_l4_end_projection_at(&*old(krnl), pagetable_ptr);
                            kernel_pagetable_mappings_projection_at(&*old(krnl), process_ptr);
                        };
                    }
                    RetValueType::ErrorVaInUse
                },
            };
            krnl.wunlock_pagetable(pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
            result
        };
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
        }
        result
    }
} // verus!
