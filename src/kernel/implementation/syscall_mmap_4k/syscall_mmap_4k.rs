use vstd::prelude::*;

use crate::*;

use super::syscall_mmap_4k_lock_helpers::{mmap_4k_lock_current_thread, mmap_4k_unlock_and_finish, mmap_4k_lock_pagetable_and_map};
use super::syscall_mmap_4k_spec::*;
use super::syscall_mmap_4k_trace::*;

verus! {
    /// Map writable, executable anonymous 4K pages into the running process.
    /// Success records an entering step that write-locks the cpu, thread, and
    /// pagetable, one step per installed directory page or published leaf, and
    /// an exiting step that unlocks all three. Failure records no step. The result is
    /// `mmap_4k_syscall_result` of the state at entry.
    #[verifier::spinoff_prover]
    pub fn syscall_mmap_4k(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize) -> (ret: RetValueType)
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
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(steps).snapshot_k() == *final(krnl),
            ret == mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range),
            ret is Success ==> range + 2 <= final(steps).nonlock_view().len() <= 4 * range + 2,
            !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
            !(ret is Success) ==> final(steps).view().len() == 0,
            ret is Success ==> mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range),
            ret is Success ==> mmap_4k_syscall_success_mapped(old(krnl), final(krnl), cpu_id, va, range),
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        if range == 0 || range > usize::MAX / 4096usize || !va_4k_valid(va) {
            proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx); }
            return RetValueType::Error;
        }

        let span = range * 4096usize;
        if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
            proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx); }
            return RetValueType::Error;
        }
        let va_range = VaRange4K::new(va, range);
        let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
        if cpu_lock_res.is_none() {
            proof { mmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::CpuIdle); }
            return RetValueType::CpuIdle;
        }
        let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
        let locked = mmap_4k_lock_current_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, Tracked(cpu_lock_perm));
        if locked.is_none() { return RetValueType::ErrorThreadKilled; }
        let (process_ptr, thread_ptr, container_ptr, alloc_ptr_4k, pagetable_ptr, quota_4k, Tracked(thread_lock_perm), Tracked(cpu_lock_perm)) = locked.unwrap();
        if quota_4k < 4 * range {
            mmap_4k_unlock_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thread_ptr, pagetable_ptr, None, Tracked(thread_lock_perm), Tracked(cpu_lock_perm));
            return RetValueType::ErrorNoQuota;
        }
        mmap_4k_lock_pagetable_and_map(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, &va_range, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, pagetable_ptr,
            Ghost(*old(lctx)), Tracked(thread_lock_perm), Tracked(cpu_lock_perm))
    }
} // verus!
