use vstd::prelude::*;
use crate::*;
use super::syscall_pci_bar_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_pci_bar_map_2m_trace::*;
use super::syscall_pci_bar_read::{pci_bar_owner_entry, pci_bar_va_2m_free};
use super::syscall_pci_bar_map_2m_finish::map_pci_bar_2m_map_and_finish;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::unmap_4k_lock_running_thread::unmap_4k_lock_current_thread;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::unmap_4k_lock_running_thread::unmap_4k_lock_current_thread;

verus! {
/// Map the 2M chunk `index` of BAR table slot `slot` at the 2M page `va` of the running process as a present, writable, non-executable
/// IO leaf. Success records an enter step that write-locks the cpu, the thread, and the pagetable; either one step per installed
/// directory page, each charged one 4K quota, or the steps that hide, flush, and reclaim the empty L1 page under the window; and an exit
/// step that installs the leaf, raises the function's mapped-BAR-page count, and releases every lock. Failure records no step. The result is `map_pci_bar_2m_syscall_result` of the state at entry.
pub fn syscall_map_pci_bar_2m(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, slot: usize,
    index: usize, va: VAddr) -> (ret: RetValueType)
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
        ret == map_pci_bar_2m_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, slot, index, va),
        !(ret is Success) ==> final(steps).view().len() == 0,
        ret is Success ==> map_pci_bar_2m_syscall_trace(final(steps).view(), cpu_id, slot, index, va),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    if !va_2m_valid(va) {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_unchanged(&*krnl, &*lctx); }
        return RetValueType::Error;
    }
    let locked = match unmap_4k_lock_current_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id) {
        Ok(e) => e,
        Err(r) => {
            proof { map_pci_bar_2m_lock_rejected_result_from_k(&*old(krnl), cpu_id, slot, index, va, r); }
            return r;
        },
    };
    let Tracked(cpu_perm) = locked.cpu_lock_perm;
    let Tracked(thread_perm) = locked.thread_lock_perm;
    let prc_ptr = locked.process_ptr;
    let thrd_ptr = locked.thread_ptr;
    let ghost entry_lctx = *old(lctx);
    let page = if slot < krnl.pci_bars.len() { krnl.pci_bars.chunk_2m(slot, index) } else { None };
    if page.is_none() {
        proof {
            process_pagetable_wf_process_at(old(krnl).prc_mp, old(krnl).pt_mp, prc_ptr);
            map_pci_bar_2m_result_from_k(&*old(krnl), cpu_id, slot, index, va, RetValueType::ErrorPciBarSlotInvalid);
        }
        krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof { steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thrd_ptr), None, None, None); }
        return RetValueType::ErrorPciBarSlotInvalid;
    }
    let addr = page.unwrap();
    let bdf = krnl.pci_bars.get(slot).bdf;
    assert(krnl.prc_mp.view().spec_index(prc_ptr).is_init() && krnl.prc_mp.view().spec_index(prc_ptr).addr() == prc_ptr) by { process_perms_wf_at(krnl.prc_mp, prc_ptr); };
    let process = krnl.prc_mp.borrow_rodata(prc_ptr).borrow();
    let pagetable = process.pagetable;
    let ctn_ptr = process.owning_container;
    let cr3 = process.cr3;
    let pcid = process.pcid;
    assert({
        &&& krnl.pt_mp.spec_index(pagetable).view().higher.cr3 == cr3
        &&& krnl.pt_mp.spec_index(pagetable).view().higher.pcid == Some(pcid)
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid
        &&& page_ptr_valid(cr3)
        &&& pcid_valid(pcid)
        &&& pcid != KERNEL_DEFAULT_PCID
        &&& krnl.pt_mp.dom().contains(pagetable)
        &&& krnl.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable
        &&& krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr
        &&& krnl.pt_mp.spec_index(pagetable).view().higher.proc_ptr == prc_ptr
        &&& krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable
    }) by {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        process_perms_wf_at(krnl.prc_mp, prc_ptr); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr);
        process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, prc_ptr);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable); krnl.pt_mp.spec_index(pagetable).view().higher.table_pages_wf_cr3_at();
    };
    proof { krnl.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr); }
    let Tracked(pagetable_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    proof { krnl.default_pagetable_wf_at(pagetable); }
    let owner_index = pci_bar_owner_entry(krnl, pagetable, bdf, Tracked(&*lctx), Tracked(&pagetable_perm));
    let (free, linked) = if owner_index.is_some() { pci_bar_va_2m_free(krnl, pagetable, va, Tracked(&*lctx), Tracked(&pagetable_perm)) } else { (false, false) };
    let quota = free && {
        assert(krnl.thrd_mp.perms_wf() && krnl.thrd_mp.spec_index(thrd_ptr).is_init()) by { thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); };
        krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_perm)).quota_4k >= 2
    };
    if !quota {
        let ret = if owner_index.is_none() { RetValueType::ErrorPciOwnerMismatch } else if !free { RetValueType::ErrorVaInUse } else { RetValueType::ErrorNoQuota };
        proof { map_pci_bar_2m_result_from_k(&*old(krnl), cpu_id, slot, index, va, ret); }
        krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
        krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
        proof { steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable), None); }
        return ret;
    }
    proof { map_pci_bar_2m_result_from_k(&*old(krnl), cpu_id, slot, index, va, RetValueType::Success); }
    map_pci_bar_2m_map_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, slot, index, va, addr, owner_index.unwrap(), linked, prc_ptr, thrd_ptr, ctn_ptr, pagetable, cr3, pcid,
        Ghost(entry_lctx), Tracked(cpu_perm), Tracked(thread_perm), Tracked(pagetable_perm));
    RetValueType::Success
}
} // verus!
