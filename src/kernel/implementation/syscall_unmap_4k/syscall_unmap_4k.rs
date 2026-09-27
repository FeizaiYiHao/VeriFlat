use vstd::prelude::*;
use crate::*;

verus! {
pub fn syscall_unmap_4k(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        ret is Success || ret is Error || ret is ErrorContainerKilled || ret is ErrorProcessKilled || ret is ErrorThreadKilled,
        ret is Success ==> range <= final(steps).nonlock_view().len() <= range + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 1,
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0 && kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
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
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    if range == 0 || range > usize::MAX / 4096usize || !va_4k_valid(va) {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return RetValueType::Error;
    }
    let span = range * 4096usize;
    if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
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
        &&& krnl.thr_mp.dom().contains(cpu.current_thread().unwrap())
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().owning_container == cpu.owning_container()
        &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view().owned_processes.view().contains(cpu.current_process().unwrap())
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_proc == cpu.current_process().unwrap()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_container == cpu.owning_container()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().state == (ThreadState::RUNNING { cpu_id })
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view().owned_threads.view().len() != 0
    }) by { reveal(container_cpu_wf); reveal(container_process_wf); reveal(thread_cpu_wf); reveal(process_thread_wf); };
    let Tracked(cpu_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_perm));
    let process_ptr = cpu.current_process().unwrap();
    let thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(&mut *lctx));
    if container_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return RetValueType::ErrorContainerKilled;
    }
    let Tracked(container_perm) = container_res.unwrap();
    let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
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
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
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
    }) by { reveal(process_thread_wf); reveal(process_cpu_wf); reveal(process_pagetable_match); reveal(process_pcid_allocator_wf); reveal(pagetable_perms_wf); reveal(PageTable::table_pages_wf); };
    assert(old(krnl).pt_mp.dom().contains(pagetable) && pagetable == old(krnl).prc_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap()).view().pagetable) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    let Tracked(pagetable_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); };
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_perm));
    let indices = va2index(va);
    let result = if pt.kernel_l4_end <= indices.0 && share_mapping_4k_source_precheck(krnl, &va_range, pagetable, Tracked(&*lctx), Tracked(&pagetable_perm)) {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        unmap_4k_range(krnl, &va_range, pagetable, thread_ptr, cpu_id, cr3, pcid, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cpu_perm), Tracked(&thread_perm), Tracked(&pagetable_perm));
        assert(va_range.view() =~= Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) by { va_range.va_range_lemma(); };
        RetValueType::Success
    } else {
        RetValueType::Error
    };
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            reveal(kernel_pagetable_nonlock_fields_unchanged);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
    }
    result
}
}
