use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_1g_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_unmap_1g_trace::unmap_1g_lock_rejected_result_from_k;
use super::syscall_unmap_1g_pagetable::unmap_1g_lock_pagetable_and_unmap;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::unmap_4k_lock_running_thread::unmap_4k_lock_current_thread;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::unmap_4k_lock_running_thread::unmap_4k_lock_current_thread;

verus! {
/// Unmap 1G pages from the running process. Success records an entering step that write-locks the cpu, the thread, and the pagetable; one step per cleared leaf, flushed cpu TLB, recorded flush, or quota refund; and an exiting step that releases them all. Failure records no step. The
/// result is `unmap_1g_syscall_result` of the state at entry, which is returned as the ghost.
pub fn syscall_unmap_1g(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, len: usize)
    -> (ret: (RetValueType, Ghost<KernelU>))
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
        ret.1@ == kernel_k_to_kernel_u(*old(krnl)),
        ret.0 == unmap_1g_syscall_result(ret.1@, cpu_id, va, len),
        !(ret.0 is Success) ==> final(steps).view().len() == 0,
        ret.0 is Success ==> unmap_1g_syscall_trace(final(steps).view(), cpu_id, va, len),
        ret.0 is Success ==> {
            let process = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap();
            let pt = old(krnl).prc_mp.spec_index(process).view().pagetable;
            let va_range = spec_va_range_1g(va, len);
            &&& final(krnl).pt_mp.dom().contains(pt)
            &&& forall|j: int| #![trigger va_range.view()[j]] 0 <= j < len ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_1g().dom().contains(va_range.view()[j])
        },
{
    let ghost entry_u = kernel_k_to_kernel_u(*krnl);
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    if len == 0 || len > usize::MAX / 0x40000000usize || !va_1g_valid(va) {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_unchanged(&*krnl, &*lctx); }
        return (RetValueType::Error, Ghost(entry_u));
    }
    let span = len * 0x40000000usize;
    if va >= usize::MAX - span || !va_1g_range_valid(va, len) {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_unchanged(&*krnl, &*lctx); }
        return (RetValueType::Error, Ghost(entry_u));
    }
    match unmap_4k_lock_current_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id) {
        Err(r) => {
            proof { unmap_1g_lock_rejected_result_from_k(&*old(krnl), cpu_id, va, len, r); }
            (r, Ghost(entry_u))
        },
        Ok(locked) => {
            let Tracked(cpu_perm) = locked.cpu_lock_perm;
            let Tracked(thread_perm) = locked.thread_lock_perm;
            let ret = unmap_1g_lock_pagetable_and_unmap(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, len, locked.process_ptr, locked.thread_ptr, Ghost(*old(lctx)),
                Tracked(cpu_perm), Tracked(thread_perm));
            (ret, Ghost(entry_u))
        },
    }
}
}
