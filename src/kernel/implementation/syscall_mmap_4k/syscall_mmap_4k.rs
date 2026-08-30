use vstd::prelude::*;

use crate::*;

use super::mmap_4k_map_range::mmap_4k_map_leaf_range;
use super::mmap_4k_precheck::{mmap_4k_precheck, Mmap4kPrecheck};
use super::syscall_mmap_4k_spec::{
    mmap_4k_lock_scope,
    mmap_4k_syscall_range_mapped,
};

verus! {

    /// Map writable, executable anonymous 4K pages into the running
    /// process. Directory construction is krnl-only; every published leaf
    /// is one user-visible krnl step.
    pub fn syscall_mmap_4k(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        va: VAddr,
        range: usize,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().state == CpuState::Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            old(krnl).all_objects_unlocked(old(lctx)),
            lock_id_aligned(old(krnl), old(lctx)),
            old(steps).steps.len() == 0,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        ensures
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(krnl).all_objects_unlocked(final(lctx)),
            lock_id_aligned(final(krnl), final(lctx)),
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            ret is Success || ret is Error || ret is ErrorVaInUse || ret is ErrorNoQuota || ret is ErrorContainerKilled || ret is ErrorProcessKilled || ret is ErrorThreadKilled,
            ret is Success ==> final(steps).steps.len() == range,
            !(ret is Success) ==> final(steps).steps.len() == 0,
            ret is Success ==> { let process_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_process->Some_0; let pagetable_ptr = old(krnl).prc_mp.spec_index(process_ptr).view().pagetable; &&& range > 0 &&& va_4k_valid(va) &&& final(krnl).pt_mp.dom().contains(pagetable_ptr) &&& mmap_4k_syscall_range_mapped(final(krnl).pt_mp.spec_index(pagetable_ptr).view(), va, range) },
    {
        if range == 0
            || range > usize::MAX / 4096usize
            || range > usize::MAX / 4usize
            || !va_4k_valid(va)
        {
            proof {
                enter_kernel_view_release_preserving_lock_id_alignment(&*krnl, &mut *lctx);
                steps.end_kernel_step(&*krnl, &*lctx);
            }
            return RetValueType::Error;
        }

        let span = range * 4096usize;
        if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
            proof {
                enter_kernel_view_release_preserving_lock_id_alignment(&*krnl, &mut *lctx);
                steps.end_kernel_step(&*krnl, &*lctx);
            }
            return RetValueType::Error;
        }
        let va_range = VaRange4K::new(va, range);

        assert({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view();
            &&& cpu.current_process is Some
            &&& cpu.current_thread is Some
            &&& krnl.ctn_mp.dom().contains(cpu.owning_container)
            &&& krnl.prc_mp.dom().contains(cpu.current_process.unwrap())
            &&& krnl.thr_mp.dom().contains(cpu.current_thread.unwrap())
            &&& krnl.thr_mp.spec_index(cpu.current_thread.unwrap()).view()
                .owning_proc == cpu.current_process.unwrap()
            &&& krnl.thr_mp.spec_index(cpu.current_thread.unwrap()).view()
                .owning_container == cpu.owning_container
            &&& krnl.thr_mp.spec_index(cpu.current_thread.unwrap()).view()
                .state == (ThreadState::RUNNING { cpu_id })
            &&& mmap_4k_no_page_locks(&*lctx)
        }) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); reveal(process_thread_wf); reveal(container_thread_wf); };

        let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
        let cpu = krnl.cpu_arr.borrow(cpu_id, Tracked(&cpu_lock_perm));
        let process_ptr = cpu.current_process.unwrap();
        let thread_ptr = cpu.current_thread.unwrap();
        let container_ptr = cpu.owning_container;

        assert(lctx.lock_id_acyclic(krnl.ctn_mp.lock_id_by_key(container_ptr))) by { reveal(lock_id_aligned); reveal(container_cpu_wf); };
        let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(&mut *lctx));
        if let (false, _) = container_res {
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                steps.end_kernel_step(&*krnl, &*lctx);
            }
            return RetValueType::ErrorContainerKilled;
        }
        let Tracked(container_lock_perm) = container_res.1.unwrap();

        assert(lctx.lock_id_acyclic(krnl.prc_mp.lock_id_by_key(process_ptr))) by { reveal(lock_id_aligned); reveal(container_process_wf); reveal(process_cpu_wf); };
        let process_res = krnl.wlock_process_unless_killed(process_ptr, Tracked(&mut *lctx));
        if let (false, _) = process_res {
            krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                steps.end_kernel_step(&*krnl, &*lctx);
            }
            return RetValueType::ErrorProcessKilled;
        }
        let Tracked(process_lock_perm) = process_res.1.unwrap();

        assert(lctx.lock_id_acyclic(krnl.thr_mp.lock_id_by_key(thread_ptr))) by { reveal(lock_id_aligned); reveal(process_thread_wf); reveal(process_perms_wf); reveal(thread_perms_wf); };
        let thread_res = krnl.wlock_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
        if let (false, _) = thread_res {
            krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
            krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                steps.end_kernel_step(&*krnl, &*lctx);
            }
            return RetValueType::ErrorThreadKilled;
        }
        let Tracked(thread_lock_perm) = thread_res.1.unwrap();

        let container_ro = krnl.ctn_mp.borrow_rodata(container_ptr);
        let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;
        let thread = krnl.thr_mp.borrow(thread_ptr, Tracked(&thread_lock_perm));
        let pagetable_ptr = thread.proc_pagetable_ptr;
        assert({
            &&& krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)
            &&& krnl.pt_mp.dom().contains(pagetable_ptr)
            &&& krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr
            &&& krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr
            &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr
            &&& krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr
            &&& !krnl.pt_mp.spec_index(pagetable_ptr).locked_by_thread(lctx.thread_id())
            &&& mmap_4k_no_page_locks(&*lctx)
        }) by { reveal(allocator_perms_wf); reveal(container_allocator_wf); reveal(process_thread_wf); reveal(process_pagetable_match); };

        let Tracked(pagetable_lock_perm) = krnl.wlock_pagetable(pagetable_ptr, Tracked(&mut *lctx));
        proof {
            assert({
                &&& mmap_4k_held_context(krnl, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, &thread_lock_perm, &pagetable_lock_perm)
                &&& mmap_4k_allocation_ready(krnl, &*lctx)
            }) by { reveal(cpu_array_wf); reveal(container_perms_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(pagetable_perms_wf); reveal(container_allocator_wf); };
        }

        let precheck = mmap_4k_precheck(krnl, &va_range, thread_ptr, pagetable_ptr, Tracked(&*lctx), Tracked(&thread_lock_perm), Tracked(&pagetable_lock_perm));
        let result;
        match precheck {
            Mmap4kPrecheck::Ready => {
                assert(krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(va_range.start)) by { assert(spec_va2index(va_range.start).0 == spec_v2l4index(va_range.start)) by (bit_vector); };
                mmap_4k_map_leaf_range(krnl, &va_range, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&thread_lock_perm), Tracked(&pagetable_lock_perm));
                proof {
                    assert(mmap_4k_syscall_range_mapped(krnl.pt_mp.spec_index(pagetable_ptr).view(), va, range)) by { va_range.va_range_lemma(); };
                }
                result = RetValueType::Success;
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

        krnl.wunlock_pagetable(pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step(&*krnl, &*lctx);
        }
        result
    }

} // verus!
