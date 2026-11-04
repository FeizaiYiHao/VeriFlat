use vstd::prelude::*;

use crate::*;

use super::syscall_mmap_2m_lock_helpers::mmap_2m_attempt;
use super::syscall_mmap_2m_spec::*;

verus! {
    /// Map writable, executable anonymous 2M pages into the running process.
    /// The call write-locks the cpu and thread once and first enters to read: it read-locks the pagetable and holds the
    /// range's 2M windows. When one of those windows has no L2 page yet, it releases only the pagetable, records the hold
    /// step with the cpu and thread still write-locked, and enters again to fill: the pagetable is write-locked while the
    /// missing L4 and L3 directories are installed and then downgraded to a read lock. Success records the entering step
    /// (after the hold step when filling), one step per installed directory page, downgrade, or published leaf, and an
    /// exiting step. Failure records no step, or the hold step and a release step when the fill section rejected the range.
    /// The result is `mmap_2m_syscall_result` of the state `ret.1` the section that decided it starts from: the entry state
    /// for the read section, or the fill section's start, which other cpus may have changed since the hold step.
    pub fn syscall_mmap_2m(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize) -> (ret: (RetValueType, Ghost<KernelU>))
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
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(steps).snapshot_k() == *final(krnl),
            ret.0 == mmap_2m_syscall_result(ret.1.view(), cpu_id, va, range),
            !(mmap_2m_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is Success)
                && !(mmap_2m_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is ErrorVaInUse) ==> ret.1.view() == kernel_k_to_kernel_u(*old(krnl)),
            ret.0 is Success ==> mmap_2m_syscall_trace(final(steps).view(), cpu_id, va, range, Mmap2mPhase::Read) && ret.1.view() == final(steps).view()[0].old_u
                || mmap_2m_syscall_trace(final(steps).view(), cpu_id, va, range, Mmap2mPhase::Fill) && ret.1.view() == final(steps).view()[1].old_u,
            ret.0 is Success ==> mmap_2m_syscall_success_mapped(final(krnl), cpu_id, va, range),
            !(ret.0 is Success) ==> final(steps).view().len() == 0 || mmap_2m_syscall_failure_trace(final(steps).view(), cpu_id, va, range) && ret.1.view() == final(steps).view()[1].old_u,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        if range == 0 || range > usize::MAX / 0x200000usize || !va_2m_valid(va) {
            proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx); }
            return (RetValueType::Error, Ghost(kernel_k_to_kernel_u(*old(krnl))));
        }
        let span = range * 0x200000usize;
        if va >= usize::MAX - span || !va_2m_range_valid(va, range) {
            proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx); }
            return (RetValueType::Error, Ghost(kernel_k_to_kernel_u(*old(krnl))));
        }
        let va_range = VaRange2M::new(va, range);
        mmap_2m_attempt(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, &va_range)
    }
} // verus!
