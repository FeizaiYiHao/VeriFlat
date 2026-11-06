use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_1g_spec::*;
use super::syscall_mmap_1g_lock::mmap_1g_attempt;

verus! {
/// Map `len` writable, executable anonymous 1G pages at `va` into the running process. Success records an entering step that write-locks the cpu, the thread, and the pagetable; one step per hidden L3 entry, flushed cpu TLB, recorded flush, reclaimed L1 or L2 page, installed L3 directory
/// page, or published leaf; and an exiting step that releases them all. Failure records no step. The result is `mmap_1g_syscall_result` of the state at entry, which is returned as the ghost.
pub fn syscall_mmap_1g(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, len: usize)
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
        ret.0 == mmap_1g_syscall_result(ret.1@, cpu_id, va, len),
        !(ret.0 is Success) ==> final(steps).view().len() == 0,
        ret.0 is Success ==> mmap_1g_syscall_trace(final(steps).view(), cpu_id, va, len),
        ret.0 is Success ==> mmap_1g_syscall_success_mapped(final(krnl), cpu_id, va, len),
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
    let va_range = VaRange1G::new(va, len);
    let ret = mmap_1g_attempt(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, len, &va_range);
    (ret, Ghost(entry_u))
}
} // verus!
