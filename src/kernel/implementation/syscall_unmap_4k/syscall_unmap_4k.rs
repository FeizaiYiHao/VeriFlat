use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_4k_spec::*;
use super::syscall_unmap_4k_helpers::unmap_4k_lock_running_thread;
use super::syscall_unmap_4k_pagetable::unmap_4k_lock_pagetable_and_unmap;

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
    let locked = match unmap_4k_lock_running_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range) {
        Ok(e) => e,
        Err(r) => { return r; },
    };
    let Tracked(cpu_perm) = locked.cpu_lock_perm;
    let Tracked(container_perm) = locked.container_lock_perm;
    let Tracked(process_perm) = locked.process_lock_perm;
    let Tracked(thread_perm) = locked.thread_lock_perm;
    unmap_4k_lock_pagetable_and_unmap(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, locked.container_ptr, locked.process_ptr, locked.thread_ptr, Ghost(*old(lctx)),
        Tracked(cpu_perm), Tracked(container_perm), Tracked(process_perm), Tracked(thread_perm))
}
}
