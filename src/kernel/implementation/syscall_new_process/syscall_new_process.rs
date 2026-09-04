use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
use super::syscall_new_process_helpers::commit_new_process;
use super::syscall_new_process_spec::kernel_u_new_process_shared;

verus! {

pub fn syscall_new_process(
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
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).steps.len() == 0,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(steps).steps.len() <= range + 2,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is Success) ==> final(steps).steps.len() == 0,
        ret is Success ==> {
            let parent_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_process->Some_0;
            &&& range > 0
            &&& final(steps).steps.len() == range + 2
            &&& final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(krnl))
            &&& exists|source_range: VaRange4K, child_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr|
                #![trigger kernel_u_new_process_shared(final(steps).steps.spec_index(0).new_u, final(steps).steps.spec_index(source_range.len as int).new_u, parent_ptr, child_ptr, &source_range), final(krnl).thr_mp.spec_index(thread_ptr)]
                source_range.wf()
                && source_range.start == va
                && source_range.len == range
                && kernel_u_create_process_changed(final(steps).steps.spec_index(0).old_u, final(steps).steps.spec_index(0).new_u, parent_ptr, child_ptr)
                && kernel_u_new_process_shared(final(steps).steps.spec_index(0).new_u, final(steps).steps.spec_index(source_range.len as int).new_u, parent_ptr, child_ptr, &source_range)
                && kernel_u_new_thread_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, child_ptr)
                && final(krnl).thr_mp.dom().contains(thread_ptr)
                && final(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED
                && final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == child_ptr
        },
        ret is Success || ret is Error || ret is ErrorContainerKilled || ret is ErrorNoPcid || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorNoQuota,
{
    if range == 0
        || range > usize::MAX / 4096usize
        || range > (usize::MAX - 4usize) / 3usize
        || !va_4k_valid(va)
    {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::Error;
    }
    let span = range * 4096usize;
    if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::Error;
    }
    let source_range = VaRange4K::new(va, range);
    proof {
        assert(krnl.cpu_arr.spec_index(cpu_id).view().view().current_process is Some && krnl.cpu_arr.spec_index(cpu_id).view().view().current_thread is Some) by { reveal(cpu_array_wf); };
    }
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    let cpu = krnl.cpu_arr.borrow(cpu_id, Tracked(&cpu_lock_perm));
    let parent_ptr = cpu.current_process.unwrap();
    let current_thread_ptr = cpu.current_thread.unwrap();
    let container_ptr = cpu.owning_container;
    proof {
        assert(krnl.prc_mp.dom().contains(parent_ptr) && krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr) by { reveal(process_cpu_wf); };
        assert(krnl.ctn_mp.dom().contains(container_ptr) && krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view().contains(parent_ptr)) by { reveal(container_process_wf); };
        assert(krnl.thr_mp.dom().contains(current_thread_ptr) && krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }) && krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr && krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
    }
    let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(&mut *lctx));
    if let (false, _) = container_res {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
        return RetValueType::ErrorContainerKilled;
    }
    let Tracked(container_lock_perm) = container_res.1.unwrap();
    let container_rodata = krnl.ctn_mp.borrow_rodata(container_ptr);
    let pcid_allocator_ptr = container_rodata.borrow().pcid_allocator;
    let scheduler_ptr = container_rodata.borrow().scheduler;
    let allocator_ptr = container_rodata.borrow().allocator_ptr_4k;
    proof {
        assert(krnl.pcid_allc_mp.dom().contains(pcid_allocator_ptr) && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().wf()) by { reveal(container_pcid_allocator_wf); reveal(pcid_allocator_perms_wf); };
        assert(!krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).locked_by_thread(lctx.thread_id())) by {
            reveal(LockedMap::typed_lock_map_aligned);
        };
    }
    let Tracked(pcid_allocator_lock_perm) = krnl.wlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx));
    let pcid_allocator = krnl.pcid_allc_mp.borrow(pcid_allocator_ptr, Tracked(&pcid_allocator_lock_perm));
    let pcid_option = pcid_allocator.find_lowest_free_nonzero();
    if let None = pcid_option {
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
        return RetValueType::ErrorNoPcid;
    }
    let pcid = pcid_option.unwrap();

    let process_res = krnl.wlock_process_unless_killed(parent_ptr, Tracked(&mut *lctx));
    if let (false, _) = process_res {
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(parent_lock_perm) = process_res.1.unwrap();
    proof {
        assert(krnl.thr_mp.dom().contains(current_thread_ptr) && krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr && krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
    }
    let thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));
    if let (false, _) = thread_res {
        proof { assert(krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); }; }
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
        return RetValueType::ErrorThreadKilled;
    }
    let Tracked(current_thread_lock_perm) = thread_res.1.unwrap();
    let source_pagetable_ptr = krnl.thr_mp.borrow(current_thread_ptr, Tracked(&current_thread_lock_perm)).proc_pagetable_ptr;
    proof {
        assert(krnl.pt_mp.dom().contains(source_pagetable_ptr) && !krnl.pt_mp.spec_index(source_pagetable_ptr).locked_by_thread(lctx.thread_id())) by { reveal(process_thread_wf); reveal(process_pagetable_match);   };
    }
    let Tracked(source_pagetable_lock_perm) = krnl.wlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx));
    let source_start_indices = va2index(va);
    proof { assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); }; }
    let source_pt = krnl.pt_mp.borrow(source_pagetable_ptr, Tracked(&source_pagetable_lock_perm));
    if source_start_indices.0 < source_pt.kernel_l4_end {
        krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        proof { assert(krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); }; }
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); }; steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::Error;
    }
    let source_ready = share_mapping_4k_source_precheck(krnl, &source_range, source_pagetable_ptr, Tracked(&*lctx), Tracked(&source_pagetable_lock_perm));
    if !source_ready {
        krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        proof { assert(krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); }; }
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); }; steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::Error;
    }
    if krnl.thr_mp.borrow(current_thread_ptr, Tracked(&current_thread_lock_perm)).quota_4k < 4 + 3 * range {
        krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        proof { assert(krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); }; }
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
        return RetValueType::ErrorNoQuota;
    }

    proof {
        assert(lctx.holds_no_allocator_locks(PageSize::SZ4k) && lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by {  reveal(LocalContext::holds_no_allocator_locks); };
    }
    commit_new_process(krnl, &source_range, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, pcid, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(pcid_allocator_lock_perm), Tracked(parent_lock_perm), Tracked(current_thread_lock_perm), Tracked(source_pagetable_lock_perm));
    RetValueType::Success
}

}
