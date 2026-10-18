use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_4k_spec::*;
use super::syscall_unmap_4k_trace::*;

verus! {
/// Unmap 4K pages from the running process. Success records an entering step that write-locks the
/// cpu, container, process, pagetable, and thread; one step per cleared leaf, flushed cpu TLB,
/// recorded flush, or quota refund; and an exiting step that unlocks all five. Failure records no
/// step. The result is `unmap_4k_syscall_result` of the state at entry.
pub fn syscall_unmap_4k(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        ret == unmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range),
        ret is Success ==> range + 3 <= final(steps).nonlock_view().len() <= range + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 4,
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0 && kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
        !(ret is Success) ==> final(steps).view().len() == 0,
        ret is Success ==> unmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range),
        ret is Success ==> {
            let process = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap();
            let pt = old(krnl).prc_mp.spec_index(process).view().pagetable;
            &&& range > 0
            &&& va_4k_range_valid(va, range)
            &&& final(krnl).pt_mp.dom().contains(pt)
            &&& final(krnl).pt_mp.spec_index(pt).view().mapping_4k() == old(krnl).pt_mp.spec_index(pt).view().mapping_4k().remove_keys(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize)).to_set())
            &&& final(krnl).pt_mp.spec_index(pt).view().mapping_2m() == old(krnl).pt_mp.spec_index(pt).view().mapping_2m()
            &&& final(krnl).pt_mp.spec_index(pt).view().mapping_1g() == old(krnl).pt_mp.spec_index(pt).view().mapping_1g()
        },
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    if range == 0 || range > usize::MAX / 4096usize || !va_4k_valid(va) {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_unchanged(&*krnl, &*lctx); }
        return RetValueType::Error;
    }
    let span = range * 4096usize;
    if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_unchanged(&*krnl, &*lctx); }
        return RetValueType::Error;
    }
    let va_range = VaRange4K::new(va, range);
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof { unmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::CpuIdle); }
        return RetValueType::CpuIdle;
    }
    let Tracked(cpu_perm) = cpu_lock_res.unwrap();
    assert({
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view();
        &&& cpu.current_process() is Some
        &&& cpu.current_thread() is Some
        &&& krnl.ctn_mp.dom().contains(cpu.owning_container())
        &&& krnl.prc_mp.dom().contains(cpu.current_process().unwrap())
        &&& krnl.thr_mp.dom().contains(cpu.current_thread().unwrap())
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().owning_container == cpu.owning_container()
        &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view_ghost().owned_processes.view().contains(cpu.current_process().unwrap())
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_proc == cpu.current_process().unwrap()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_container == cpu.owning_container()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().state == (ThreadState::RUNNING { cpu_id })
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view().owned_threads.view().len() != 0
        &&& !krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view().zombie
        &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view_rodata().view().depth == cpu.view().container_depth
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().container_depth == cpu.view().container_depth
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().depth == cpu.view().process_depth
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().container_depth == cpu.view().container_depth
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().process_depth == cpu.view().process_depth
    }) by {
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
        container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id);
        container_process_wf_container_at(krnl.ctn_mp, krnl.prc_mp, cpu.owning_container, cpu.current_process.unwrap()); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, cpu.current_thread.unwrap());
        process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, cpu.current_process.unwrap());
    };
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_perm));
    let process_ptr = cpu.current_process().unwrap();
    let thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(&mut *lctx));
    if container_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
            unmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::ErrorContainerKilled);
        }
        return RetValueType::ErrorContainerKilled;
    }
    let Tracked(container_perm) = container_res.unwrap();
    let container = krnl.ctn_mp.borrow_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_perm));
    if container.zombie {
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
            unmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::ErrorContainerZombie);
        }
        return RetValueType::ErrorContainerZombie;
    }
    let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), None, None, None, None);
            unmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::ErrorProcessKilled);
        }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(process_perm) = process_res.unwrap();
    let thread_res = krnl.wlock_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, None, None);
            unmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::ErrorThreadKilled);
        }
        return RetValueType::ErrorThreadKilled;
    }
    let Tracked(thread_perm) = thread_res.unwrap();
    let process = krnl.prc_mp.borrow_rodata(process_ptr).borrow();
    let pagetable = process.pagetable;
    let cr3 = process.cr3;
    let pcid = process.pcid;
    assert({
        &&& krnl.pt_mp.dom().contains(pagetable)
        &&& krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable
        &&& krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3
        &&& krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid)
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid
        &&& page_ptr_valid(cr3)
        &&& pcid_valid(pcid)
        &&& pcid != KERNEL_DEFAULT_PCID
    }) by {
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr);
        process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, process_ptr); pagetable_perms_wf_at(krnl.pt_mp, pagetable); reveal(PageTable::table_pages_wf);
    };
    assert(old(krnl).pt_mp.dom().contains(pagetable) && pagetable == old(krnl).prc_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap()).view().pagetable) by {
        process_cpu_wf_at(old(krnl).prc_mp, old(krnl).cpu_arr, cpu_id); process_pagetable_match_process_at(old(krnl).prc_mp, old(krnl).pt_mp, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap());
    };
    let Tracked(pagetable_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    assert(krnl.pt_mp.perms_wf()) by { pagetable_perms_wf_map(krnl.pt_mp); };
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_perm));
    let indices = va2index(va);
    proof { assert(va_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) })) by { va_range.va_range_lemma(); }; }
    if pt.kernel_l4_end <= indices.0 && share_mapping_4k_source_precheck(krnl, &va_range, pagetable, Tracked(&*lctx), Tracked(&pagetable_perm)) {
        proof { unmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::Success); }
        krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::Unmap4k { range: va_range, unmapped: 0, flushed: false })), Tracked(&*lctx), Tracked(&thread_perm));
        proof {
            let ghost entered_k = *krnl;
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
            assert(unmap_4k_trace_after_enter(steps.view(), cpu_id, va_range)) by {
                kernel_thread_context_lock_states_and_progress_changed_implies_u_step(&*old(krnl), &entered_k, old(lctx), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable);
                unmap_4k_enter_step_from_u(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id, container_ptr, process_ptr, thread_ptr, va_range);
                unmap_4k_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(entered_k), cpu_id, va_range);
            };
        }
        let ghost entered = steps.view();
        unmap_4k_range(krnl, &va_range, pagetable, thread_ptr, cpu_id, cr3, pcid, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cpu_perm), Tracked(&thread_perm), Tracked(&pagetable_perm));
        let ghost range_steps = steps.view();
        let ghost exit_start = *krnl;
        let ghost exit_lctx = *lctx;
        proof { assert(unmap_4k_trace_after_range(range_steps, cpu_id, va_range)) by { unmap_4k_trace_range_steps(&*steps, entered, cpu_id, va_range); }; }
        assert(va_range.view() =~= Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) by { va_range.va_range_lemma(); };
        krnl.set_thread_syscall_progress(thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_perm));
        krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            let ghost exit_k = *krnl;
            steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thread_ptr);
            assert(unmap_4k_syscall_trace(steps.view(), cpu_id, va, range)) by {
                kernel_thread_context_lock_states_and_progress_changed_implies_u_step(&exit_start, &exit_k, &exit_lctx, cpu_id, container_ptr, process_ptr, thread_ptr, pagetable);
                unmap_4k_exit_step_from_u(kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(exit_k), cpu_id, container_ptr, process_ptr, thread_ptr);
                unmap_4k_trace_exit_step(&*steps, range_steps, kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(exit_k), cpu_id, va, range);
            };
        }
        return RetValueType::Success;
    }
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, Some(pagetable), None);
        unmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::Error);
    }
    RetValueType::Error
}
}
