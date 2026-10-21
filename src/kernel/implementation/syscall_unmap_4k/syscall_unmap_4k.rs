use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_4k_spec::*;
use super::syscall_unmap_4k_helpers::unmap_4k_lock_running_thread;
use super::syscall_unmap_4k_pagetable::unmap_4k_lock_pagetable_and_unmap;

verus! {
/// Unmap 4K pages from the running process. Success records an entering step that write-locks the
/// cpu, container, process, and thread and read-locks the pagetable; one step per cleared leaf,
/// flushed cpu TLB, recorded flush, or quota refund; and an exiting step that releases all five.
/// Inside the 2M windows of the range only its pages change. Failure records no step. The result
/// is `unmap_4k_syscall_result` of the state at entry.
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
            let va_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
            &&& range > 0
            &&& va_4k_range_valid(va, range)
            &&& final(krnl).pt_mp.dom().contains(pt)
            &&& forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_4k().dom().contains(va_range.view()[j])
            &&& forall|j: int, v: VAddr|
                #![trigger va_range.view()[j], pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_4k().dom().contains(v)]
                #![trigger va_range.view()[j], pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_4k().dom().contains(v)]
                0 <= j < range && spec_v2l4index(v) == spec_v2l4index(va_range.view()[j]) && spec_v2l3index(v) == spec_v2l3index(va_range.view()[j]) && spec_v2l2index(v) == spec_v2l2index(va_range.view()[j])
                    && !va_range.view().contains(v) ==> {
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_4k().dom().contains(v)
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_4k().dom().contains(v)
                        ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_4k().spec_index(v)
                }
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_1g()
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
