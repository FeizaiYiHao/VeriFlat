use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_4k_read_enter::mmap_4k_try_read_enter;
use super::syscall_mmap_4k_spec::*;
use super::syscall_mmap_4k_trace::*;

verus! {
/// Write-locks `cpu_id` while it runs a live thread, then that thread, and with enough quota maps `va_range` through
/// `mmap_4k_try_read_enter`, which keeps both locks to fill when reading finds a 2M window of the range missing. Returns the
/// result and the state of the section that decided it.
pub(super) fn mmap_4k_attempt(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange4K,
) -> (ret: (RetValueType, Ghost<KernelU>))
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        *va_range == spec_va_range_4k(va, range),
        va_range.wf(),
        va_range.len > 0,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        ret.0 == mmap_4k_syscall_result(ret.1.view(), cpu_id, va, range),
        !(mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is Success)
            && !(mmap_4k_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range) is ErrorVaInUse) ==> ret.1.view() == kernel_k_to_kernel_u(*old(krnl)),
        ret.0 is Success ==> mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range, Mmap4kPhase::Read) && ret.1.view() == final(steps).view()[0].old_u
            || mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range, Mmap4kPhase::Fill) && ret.1.view() == final(steps).view()[1].old_u,
        ret.0 is Success ==> mmap_4k_syscall_success_mapped(final(krnl), cpu_id, va, range),
        !(ret.0 is Success) ==> final(steps).view().len() == 0 || mmap_4k_syscall_failure_trace(final(steps).view(), cpu_id, va, range) && ret.1.view() == final(steps).view()[1].old_u,
{
    let ghost entry_lctx = *lctx;
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof { mmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::CpuIdle, None, None); }
        return (RetValueType::CpuIdle, Ghost(kernel_k_to_kernel_u(*old(krnl))));
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    let locked = mmap_4k_lock_current_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
    if locked.is_none() {
        proof { mmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::ErrorThreadKilled, None, None); }
        return (RetValueType::ErrorThreadKilled, Ghost(kernel_k_to_kernel_u(*old(krnl))));
    }
    let (prc_ptr, thrd_ptr, ctn_ptr, alloc_ptr_4k, pagetable_ptr, quota_4k, Tracked(thread_lock_perm), Tracked(cpu_lock_perm)) = locked.unwrap();
    if quota_4k < 4 * range {
        proof { mmap_4k_result_from_k(&*old(krnl), cpu_id, va, range, RetValueType::ErrorNoQuota, None, None); }
        mmap_4k_unlock_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thrd_ptr, Tracked(thread_lock_perm), Tracked(cpu_lock_perm));
        return (RetValueType::ErrorNoQuota, Ghost(kernel_k_to_kernel_u(*old(krnl))));
    }
    mmap_4k_try_read_enter(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, va_range, alloc_ptr_4k, thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr,
        Ghost(entry_lctx), Tracked(thread_lock_perm), Tracked(cpu_lock_perm))
}
} // verus!
