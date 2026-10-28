use vstd::prelude::*;

use crate::*;

use super::syscall_mmap_4k_lock_helpers::mmap_4k_attempt;
use super::syscall_mmap_4k_spec::*;

verus! {
    /// Map writable, executable anonymous 4K pages into the running process.
    /// The call write-locks the cpu and thread once and first enters to read: it read-locks the pagetable and holds the
    /// range's 2M windows. When one of those windows has no L2 page yet, it releases only the pagetable, records the hold
    /// step with the cpu and thread still write-locked, and enters again to fill: the pagetable is write-locked while the
    /// missing L4 and L3 directories are installed and then downgraded to a read lock. Success records the entering step
    /// (after the hold step when filling), one step per installed directory page, downgrade, or published leaf, and an
    /// exiting step. Failure records no step, or the hold step and a release step when the fill section rejected the range.
    /// The result is `mmap_4k_syscall_result` of the state `ret.1` the section that decided it starts from: the entry state
    /// for the read section, or the fill section's start, which other cpus may have changed since the hold step.
    pub fn syscall_mmap_4k(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize)
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
            old(steps).nonlock_view().len() == 0,
            old(steps).view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(steps).snapshot_k() == *final(krnl),
            ret.0 == mmap_4k_syscall_result(ret.1@, cpu_id, va, range),
            !(mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is Success)
                && !(mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is ErrorVaInUse) ==> ret.1@ == kernel_k_to_kernel_u(*old(krnl)),
            ret.0 is Success ==> range + 2 <= final(steps).nonlock_view().len() <= 4 * range + 3,
            ret.0 is Success ==> mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range, Mmap4kPhase::Read) && ret.1@ == final(steps).view()[0].old_u
                || mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range, Mmap4kPhase::Fill) && ret.1@ == final(steps).view()[1].old_u,
            ret.0 is Success ==> mmap_4k_syscall_success_mapped(final(krnl), cpu_id, va, range),
            !(ret.0 is Success) ==> final(steps).nonlock_view().len() == 0,
            !(ret.0 is Success) ==> final(steps).view().len() == 0 || mmap_4k_syscall_failure_trace(final(steps).view(), cpu_id, va, range) && ret.1@ == final(steps).view()[1].old_u,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        if range == 0 || range > usize::MAX / 4096usize || !va_4k_valid(va) {
            proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx); }
            return (RetValueType::Error, Ghost(kernel_k_to_kernel_u(*old(krnl))));
        }
        let span = range * 4096usize;
        if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
            proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx); }
            return (RetValueType::Error, Ghost(kernel_k_to_kernel_u(*old(krnl))));
        }
        let va_range = VaRange4K::new(va, range);
        mmap_4k_attempt(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, &va_range)
    }
} // verus!
