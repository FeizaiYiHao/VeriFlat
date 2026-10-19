use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_4k_spec::*;
use super::syscall_unmap_4k_trace::*;
use super::syscall_unmap_4k_helpers::{unmap_4k_lock_running_thread, unmap_4k_unmap_and_finish};

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
    let locked = match unmap_4k_lock_running_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range) {
        Ok(e) => e,
        Err(r) => { return r; },
    };
    let container_ptr = locked.container_ptr;
    let process_ptr = locked.process_ptr;
    let thread_ptr = locked.thread_ptr;
    let Tracked(cpu_perm) = locked.cpu_lock_perm;
    let Tracked(container_perm) = locked.container_lock_perm;
    let Tracked(process_perm) = locked.process_lock_perm;
    let Tracked(thread_perm) = locked.thread_lock_perm;
    assert(krnl.prc_mp.view().spec_index(process_ptr).is_init() && krnl.prc_mp.view().spec_index(process_ptr).addr() == process_ptr) by { process_perms_wf_at(krnl.prc_mp, process_ptr); };
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
        process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, process_ptr); pagetable_perms_wf_at(krnl.pt_mp, pagetable); krnl.pt_mp.spec_index(pagetable).view().table_pages_wf_cr3_at();
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
        unmap_4k_unmap_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, &va_range, container_ptr, process_ptr, thread_ptr, pagetable, cr3, pcid,
            Ghost(*old(lctx)), Tracked(cpu_perm), Tracked(container_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(pagetable_perm));
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
