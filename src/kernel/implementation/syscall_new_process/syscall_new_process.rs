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
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr,
    range: usize, initial_regs: &Registers,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
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
        !(ret is SuccessPairUsize) ==> final(steps).steps.len() == 0,
        ret is SuccessPairUsize ==> {
            let parent_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process->Some_0;
            let child_ptr = ret->SuccessPairUsize_value1;
            let thread_ptr = ret->SuccessPairUsize_value2;
            let source_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
            &&& range > 0
            &&& final(steps).steps.len() == range + 2
            &&& final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(krnl))
            &&& source_range.wf()
            &&& kernel_u_create_process_changed(final(steps).steps.spec_index(0).old_u, final(steps).steps.spec_index(0).new_u, parent_ptr, child_ptr)
            &&& kernel_u_new_process_shared(final(steps).steps.spec_index(0).new_u, final(steps).steps.spec_index(source_range.len as int).new_u, parent_ptr, child_ptr, &source_range)
            &&& kernel_u_new_thread_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, child_ptr)
            &&& final(krnl).thr_mp.dom().contains(thread_ptr)
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == child_ptr
        },
        ret is SuccessPairUsize || ret is Error || ret is ErrorContainerKilled || ret is ErrorNoPcid || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorNoQuota,
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
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let parent_ptr = cpu.current_process().unwrap();
    let current_thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    proof {
        assert(krnl.prc_mp.dom().contains(parent_ptr) && krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr) by { reveal(process_cpu_wf); };
        assert(krnl.thr_mp.dom().contains(current_thread_ptr) && krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }) && krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr && krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
        assert(krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(container_process_wf); };
    }
    let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(&mut *lctx));
    if container_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorContainerKilled;
    }
    let Tracked(container_lock_perm) = container_res.unwrap();
    let container_rodata = krnl.ctn_mp.borrow_rodata(container_ptr);
    let pcid_allocator_ptr = container_rodata.borrow().pcid_allocator;
    let scheduler_ptr = container_rodata.borrow().scheduler;
    let allocator_ptr = container_rodata.borrow().allocator_ptr_4k;
    proof {
        assert(krnl.pcid_allc_mp.dom().contains(pcid_allocator_ptr) && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().wf() && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().owning_container.view() == container_ptr) by { reveal(container_pcid_allocator_wf); reveal(pcid_allocator_perms_wf); };
    }
    let Tracked(pcid_allocator_lock_perm) = krnl.wlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx));
    let pcid_allocator = krnl.pcid_allc_mp.borrow_typed(pcid_allocator_ptr, Ghost(lctx.pcid_allocator_lock_map()), Tracked(&*lctx), Tracked(&pcid_allocator_lock_perm));
    let pcid = match pcid_allocator.find_lowest_free_nonzero() {
        Some(pcid) => pcid,
        None => {
            krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
            proof { assert(!krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view().is_empty()) by { reveal(container_process_wf); }; }
            krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof { steps.end_kernel_step(&*krnl, &*lctx); }
            return RetValueType::ErrorNoPcid;
        },
    };

    let process_res = krnl.wlock_process_unless_killed(parent_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        proof { assert(!krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view().is_empty()) by { reveal(container_process_wf); }; }
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(parent_lock_perm) = process_res.unwrap();
    let thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        proof { assert(krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); }; }
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        proof { assert(!krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view().is_empty()) by { reveal(container_process_wf); }; }
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorThreadKilled;
    }
    let Tracked(current_thread_lock_perm) = thread_res.unwrap();
    let thread_ref = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
    let source_pagetable_ptr = thread_ref.proc_pagetable_ptr;
    if thread_ref.quota_4k < 4 + 3 * range {
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        proof { assert(krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); }; }
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        proof { assert(!krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view().is_empty()) by { reveal(container_process_wf); }; }
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorNoQuota;
    }
    proof {
        assert(krnl.pt_mp.dom().contains(source_pagetable_ptr) && !lctx.pagetable_lock_map().dom().contains(source_pagetable_ptr)) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
    }
    let Tracked(source_pagetable_lock_perm) = krnl.wlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx));
    let source_start_indices = va2index(va);
    proof { assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); }; }
    let source_pt = krnl.pt_mp.borrow_typed(source_pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&source_pagetable_lock_perm));
    let source_ready = if source_start_indices.0 < source_pt.kernel_l4_end {
        false
    } else {
        share_mapping_4k_source_precheck(krnl, &source_range, source_pagetable_ptr, Tracked(&*lctx), Tracked(&source_pagetable_lock_perm))
    };
    if !source_ready {
        krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        proof { assert(krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); }; }
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        proof { assert(!krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view().is_empty()) by { reveal(container_process_wf); }; }
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::Error;
    }

    proof {
        assert(lctx.holds_no_allocator_locks(PageSize::SZ4k) && lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by { reveal(LocalContext::holds_no_allocator_locks); };
    }
    let (child_ptr, thread_ptr) = commit_new_process(
        krnl, &source_range, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr,
        current_thread_ptr, scheduler_ptr, allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, pcid,
        Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(pcid_allocator_lock_perm), Tracked(parent_lock_perm),
        Tracked(current_thread_lock_perm), Tracked(source_pagetable_lock_perm), initial_regs,
    );
    RetValueType::SuccessPairUsize { value1: child_ptr, value2: thread_ptr }
}
}
