use vstd::prelude::*;
use crate::*;
use super::syscall_new_container_helpers::commit_new_container;

verus! {

pub fn syscall_new_container(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId,
    funding_page_count: usize,
    process_quota_4k: usize,
    initial_regs: &Registers,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state
            == CpuState::Running,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).steps.len() == 0,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).steps.len() <= 1,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is SuccessThreeUsize) ==> final(steps).steps.len() == 0,
        ret is SuccessThreeUsize ==> {
            let parent_container_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
            let child_container_ptr = ret->SuccessThreeUsize_value1;
            let child_process_ptr = ret->SuccessThreeUsize_value2;
            let child_thread_ptr = ret->SuccessThreeUsize_value3;
            &&& final(krnl).ctn_mp.dom().contains(child_container_ptr)
            &&& final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr)
            &&& final(krnl).prc_mp.dom().contains(child_process_ptr)
            &&& final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().owning_container == child_container_ptr
            &&& final(krnl).thr_mp.dom().contains(child_thread_ptr)
            &&& final(krnl).thr_mp.spec_index(child_thread_ptr).view().state is SCHEDULED
            &&& final(krnl).thr_mp.spec_index(child_thread_ptr).view().owning_container == child_container_ptr
            &&& final(krnl).thr_mp.spec_index(child_thread_ptr).view().owning_proc == child_process_ptr
        },
        ret is SuccessThreeUsize
            || ret is Error
            || ret is ErrorContainerKilled
            || ret is ErrorProcessKilled
            || ret is ErrorThreadKilled
            || ret is ErrorNoQuota,
{
    if process_quota_4k > funding_page_count
        || funding_page_count > usize::MAX - 9
    {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(
                &*krnl,
                &mut *lctx,
            );
            steps.end_kernel_step(&*krnl, &*lctx);
        }
        return RetValueType::Error;
    }

    proof {
        assert({
            &&& krnl.cpu_arr.spec_index(cpu_id)
                .view().view().view().current_process is Some
            &&& krnl.cpu_arr.spec_index(cpu_id)
                .view().view().view().current_thread is Some
        }) by {
            reveal(cpu_array_wf);
        };
    }
    let Tracked(cpu_lock_perm) =
        krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let parent_container_ptr = cpu.owning_container();
    let parent_process_ptr = cpu.current_process().unwrap();
    let current_thread_ptr = cpu.current_thread().unwrap();
    proof {
        assert(krnl.ctn_mp.dom().contains(parent_container_ptr)) by {
            reveal(container_cpu_wf);
        };
        assert({
            &&& krnl.prc_mp.dom().contains(parent_process_ptr)
            &&& krnl.prc_mp.spec_index(parent_process_ptr)
                .view_rodata().view().owning_container
                == parent_container_ptr
        }) by {
            reveal(process_cpu_wf);
        };
        assert({
            &&& krnl.thr_mp.dom().contains(current_thread_ptr)
            &&& krnl.thr_mp.spec_index(current_thread_ptr)
                .view().state == (ThreadState::RUNNING { cpu_id })
            &&& krnl.thr_mp.spec_index(current_thread_ptr)
                .view().owning_container == parent_container_ptr
            &&& krnl.thr_mp.spec_index(current_thread_ptr)
                .view().owning_proc == parent_process_ptr
        }) by {
            reveal(thread_cpu_wf);
            reveal(process_thread_wf);
        };
    }
    let container_res = krnl.wlock_container_unless_killed(
        parent_container_ptr,
        Tracked(&mut *lctx),
    );
    if let (false, _) = container_res {
        krnl.wunlock_cpu(
            cpu_id,
            Tracked(&mut *lctx),
            Tracked(cpu_lock_perm),
        );
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorContainerKilled;
    }
    let Tracked(container_lock_perm) = container_res.1.unwrap();
    proof { assert(!krnl.ctn_mp.spec_index(parent_container_ptr).view().owned_processes.view().is_empty()) by { reveal(container_process_wf); }; }
    let parent_depth = krnl.ctn_mp
        .borrow_rodata(parent_container_ptr).borrow().depth;
    if parent_depth >= MAX_CONTAINER_TREE_DEPTH {
        krnl.wunlock_container(
            parent_container_ptr,
            Tracked(&mut *lctx),
            Tracked(container_lock_perm),
        );
        krnl.wunlock_cpu(
            cpu_id,
            Tracked(&mut *lctx),
            Tracked(cpu_lock_perm),
        );
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::Error;
    }

    let process_res = krnl.wlock_process_unless_killed(parent_process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if let (false, _) = process_res {
        krnl.wunlock_container(
            parent_container_ptr,
            Tracked(&mut *lctx),
            Tracked(container_lock_perm),
        );
        krnl.wunlock_cpu(
            cpu_id,
            Tracked(&mut *lctx),
            Tracked(cpu_lock_perm),
        );
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(process_lock_perm) = process_res.1.unwrap();
    proof { assert(krnl.prc_mp.spec_index(parent_process_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); }; }
    let thread_res = krnl.wlock_thread_unless_killed(
        current_thread_ptr,
        Tracked(&mut *lctx),
    );
    if let (false, _) = thread_res {
        krnl.wunlock_process(
            parent_process_ptr,
            Tracked(&mut *lctx),
            Tracked(process_lock_perm),
        );
        krnl.wunlock_container(
            parent_container_ptr,
            Tracked(&mut *lctx),
            Tracked(container_lock_perm),
        );
        krnl.wunlock_cpu(
            cpu_id,
            Tracked(&mut *lctx),
            Tracked(cpu_lock_perm),
        );
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorThreadKilled;
    }
    let Tracked(thread_lock_perm) = thread_res.1.unwrap();
    let thread = krnl.thr_mp.borrow_typed(
        current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let quota_4k = thread.quota_4k;
    let quota_2m = thread.quota_2m;
    let source_pagetable_ptr = thread.proc_pagetable_ptr;
    let required_4k = 9usize + funding_page_count;
    let quota_available =
        quota_4k >= required_4k && quota_2m >= 2;
    if !quota_available {
        krnl.wunlock_thread(
            current_thread_ptr,
            Tracked(&mut *lctx),
            Tracked(thread_lock_perm),
        );
        krnl.wunlock_process(
            parent_process_ptr,
            Tracked(&mut *lctx),
            Tracked(process_lock_perm),
        );
        krnl.wunlock_container(
            parent_container_ptr,
            Tracked(&mut *lctx),
            Tracked(container_lock_perm),
        );
        krnl.wunlock_cpu(
            cpu_id,
            Tracked(&mut *lctx),
            Tracked(cpu_lock_perm),
        );
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorNoQuota;
    }

    proof {
        assert({
            &&& krnl.pt_mp.dom().contains(source_pagetable_ptr)
            &&& !lctx.pagetable_lock_map().dom().contains(source_pagetable_ptr)
        }) by {
            reveal(process_thread_wf);
            reveal(process_pagetable_match);
        };
    }
    let Tracked(source_pagetable_lock_perm) = krnl.wlock_pagetable(
        source_pagetable_ptr,
        Tracked(&mut *lctx),
    );
    proof {
        assert({
            &&& lctx.holds_no_allocator_locks(PageSize::SZ4k)
            &&& lctx.holds_no_allocator_locks(PageSize::SZ2m)
            &&& lctx.holds_no_allocator_locks(PageSize::SZ1g)
            &&& lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)
        }) by {
            reveal(LocalContext::holds_no_allocator_locks);
        };
        assert(
            krnl.ctn_mp.spec_index(parent_container_ptr)
                .view_rodata().view().depth < usize::MAX
        ) by {
            assert(MAX_CONTAINER_TREE_DEPTH < usize::MAX) by (compute);
        };
    }
    let (
        child_container_ptr,
        child_process_ptr,
        child_thread_ptr,
    ) = commit_new_container(
        krnl,
        Tracked(&mut *lctx),
        Tracked(&mut *steps),
        cpu_id,
        parent_container_ptr,
        parent_process_ptr,
        current_thread_ptr,
        source_pagetable_ptr,
        funding_page_count,
        process_quota_4k,
        Tracked(cpu_lock_perm),
        Tracked(container_lock_perm),
        Tracked(process_lock_perm),
        Tracked(thread_lock_perm),
        Tracked(source_pagetable_lock_perm),
        initial_regs,
    );
    RetValueType::SuccessThreeUsize { value1: child_container_ptr, value2: child_process_ptr, value3: child_thread_ptr }
}

}
