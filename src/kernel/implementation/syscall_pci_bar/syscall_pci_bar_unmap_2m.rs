use vstd::prelude::*;
use crate::*;
use super::syscall_pci_bar_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_pci_bar_unmap_2m_trace::*;
use super::syscall_pci_bar_unmap_2m_finish::unmap_pci_bar_2m_unmap_and_finish;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::unmap_4k_lock_running_thread::unmap_4k_lock_current_thread;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::unmap_4k_lock_running_thread::unmap_4k_lock_current_thread;

verus! {
/// Unmap the 2M BAR page mapped at `va` from the running process. Success records a hide step that write-locks the cpu, the thread,
/// and the pagetable and hides the leaf; one step per flushed cpu TLB; a step recording the flush; and an exit step that removes the
/// leaf, lowers its function's mapped-BAR-page count, and releases all three locks. Failure records no step. The result is
/// `unmap_pci_bar_2m_syscall_result` of the state at entry.
pub fn syscall_unmap_pci_bar_2m(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr)
    -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
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
        ret == unmap_pci_bar_2m_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va),
        !(ret is Success) ==> final(steps).view().len() == 0,
        ret is Success ==> unmap_pci_bar_2m_syscall_trace(final(steps).view(), cpu_id, va),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    if !va_2m_valid(va) {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_unchanged(&*krnl, &*lctx); }
        return RetValueType::Error;
    }
    let locked = match unmap_4k_lock_current_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id) {
        Ok(e) => e,
        Err(r) => {
            proof { unmap_pci_bar_2m_lock_rejected_result_from_k(&*old(krnl), cpu_id, va, r); }
            return r;
        },
    };
    let Tracked(cpu_perm) = locked.cpu_lock_perm;
    let Tracked(thread_perm) = locked.thread_lock_perm;
    let prc_ptr = locked.process_ptr;
    let thrd_ptr = locked.thread_ptr;
    let ghost entry_lctx = *old(lctx);
    assert(krnl.prc_mp.view().spec_index(prc_ptr).is_init() && krnl.prc_mp.view().spec_index(prc_ptr).addr() == prc_ptr) by { process_perms_wf_at(krnl.prc_mp, prc_ptr); };
    let process = krnl.prc_mp.borrow_rodata(prc_ptr).borrow();
    let pagetable = process.pagetable;
    let cr3 = process.cr3;
    let pcid = process.pcid;
    assert({
        &&& krnl.pt_mp.dom().contains(pagetable)
        &&& krnl.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable
        &&& krnl.pt_mp.spec_index(pagetable).view().higher.cr3 == cr3
        &&& krnl.pt_mp.spec_index(pagetable).view().higher.pcid == Some(pcid)
        &&& krnl.pt_mp.spec_index(pagetable).view().higher.proc_ptr == prc_ptr
        &&& krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid
        &&& page_ptr_valid(cr3)
        &&& pcid_valid(pcid)
        &&& pcid != KERNEL_DEFAULT_PCID
    }) by {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        process_perms_wf_at(krnl.prc_mp, prc_ptr); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, prc_ptr); pagetable_perms_wf_at(krnl.pt_mp, pagetable);
        krnl.pt_mp.spec_index(pagetable).view().higher.table_pages_wf_cr3_at();
    };
    proof { krnl.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr); }
    let Tracked(pagetable_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    proof { krnl.default_pagetable_wf_at(pagetable); }
    match unmap_pci_bar_2m_io_leaf(krnl, pagetable, va, Tracked(&*lctx), Tracked(&pagetable_perm)) {
        Some((addr, l2_ptr)) => {
            proof { unmap_pci_bar_2m_result_from_k(&*old(krnl), cpu_id, va, RetValueType::Success); }
            unmap_pci_bar_2m_unmap_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, addr, l2_ptr, prc_ptr, thrd_ptr, pagetable, cr3, pcid, Ghost(entry_lctx),
                Tracked(cpu_perm), Tracked(thread_perm), Tracked(pagetable_perm));
            RetValueType::Success
        },
        None => {
            proof { unmap_pci_bar_2m_result_from_k(&*old(krnl), cpu_id, va, RetValueType::ErrorPciBarNotMapped); }
            krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
            krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
            krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
            proof { steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable), None); }
            RetValueType::ErrorPciBarNotMapped
        },
    }
}

/// The address of the present IO 2M leaf `va` of the write-held page table `pagetable_ptr` and the L2 page holding it, or None when
/// `va` is no such leaf. No krnl or LocalContext state changes.
fn unmap_pci_bar_2m_io_leaf(krnl: &KernelK, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&LocalContext>, Tracked(pagetable_perm): Tracked<&LockPerm>)
    -> (ret: Option<(PAddr, PageMapPtr)>)
    requires
        krnl.inv(),
        krnl.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.pt_mp.spec_index(pagetable_ptr).view().higher.kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        va_2m_valid(va),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == lctx.thread_id(),
        pagetable_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
    ensures
        ({
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            &&& (ret is Some) == (table.mapping_2m().dom().contains(va) && table.mapping_2m()[va].present && table.mapping_2m()[va].is_io)
            &&& ret is Some ==> ret->Some_0.0 == table.mapping_2m()[va].addr
            &&& ret is Some ==> table.spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some
                && table.spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == ret->Some_0.1
        }),
{
    let indices = va2index(va);
    proof {
        assert(indices.0 == spec_v2l4index(va) && indices.1 == spec_v2l3index(va) && indices.2 == spec_v2l2index(va) && spec_index2va((indices.0, indices.1, indices.2, 0usize)) == va) by {
            broadcast use spec_va_2m_valid_index_roundtrip;
        };
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf_mapping_2m_at(indices.0, indices.1, indices.2);
    }
    let pt = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_perm));
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
    let l4 = match pt.higher.get_entry_l4(indices.0) { Some(e) => e, None => { return None; } };
    let l3 = match pt.higher.get_entry_l3(indices.0, indices.1, &l4) { Some(e) => e, None => { return None; } };
    let leaf = match pt.higher.get_entry_2m_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3) { Some(e) => e, None => { return None; } };
    if leaf.perm.present && leaf.perm.is_io { Some((leaf.addr, l3.addr)) } else { None }
}
} // verus!
