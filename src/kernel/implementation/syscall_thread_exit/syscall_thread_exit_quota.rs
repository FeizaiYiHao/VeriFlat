use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_quota_helpers::{thread_exit_return_quota_4k, thread_exit_return_quota_2m, thread_exit_return_quota_1g};

verus! {
/// Return the whole `size` quota of the running last thread `thrd_ptr` and of its process `prc_ptr` to the `size`
/// allocator of their container `ctn_ptr` under that allocator's quota lock, and record the return as the
/// thread's progress.
pub(super) fn thread_exit_return_quota(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    size: PageSize, Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)]
            old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().contains(prc_ptr),
        old(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().contains(thrd_ptr),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
        !old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        progress_peer_of(old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()) is None,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        kernel_thread_exit_quota_returned(old(krnl), final(krnl), thrd_ptr, size),
        *final(krnl) == (KernelK {
            prc_mp: final(krnl).prc_mp, thrd_mp: final(krnl).thrd_mp, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp,
            ..*old(krnl)
        }),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, prc_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr).view() == match size {
            PageSize::SZ4k => Process { quota_4k: 0, ..old(krnl).prc_mp.spec_index(prc_ptr).view() },
            PageSize::SZ2m => Process { quota_2m: 0, ..old(krnl).prc_mp.spec_index(prc_ptr).view() },
            PageSize::SZ1g => Process { quota_1g: 0, ..old(krnl).prc_mp.spec_index(prc_ptr).view() },
        },
        final(krnl).prc_mp.spec_index(prc_ptr).view_rodata() == old(krnl).prc_mp.spec_index(prc_ptr).view_rodata(),
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost() == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost(),
        final(krnl).prc_mp.spec_index(prc_ptr).locking_thread() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread(),
        final(krnl).prc_mp.spec_index(prc_ptr).being_killed() == old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        final(krnl).thrd_mp.dom() == old(krnl).thrd_mp.dom(),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == match size {
            PageSize::SZ4k => Thread { quota_4k: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: size })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() },
            PageSize::SZ2m => Thread { quota_2m: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: size })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() },
            PageSize::SZ1g => Thread { quota_1g: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: size })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() },
        },
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
{
    match size {
        PageSize::SZ4k => thread_exit_return_quota_4k(krnl, Tracked(&mut *lctx), ctn_ptr, prc_ptr, thrd_ptr, Tracked(process_lock_perm), Tracked(thread_lock_perm)),
        PageSize::SZ2m => thread_exit_return_quota_2m(krnl, Tracked(&mut *lctx), ctn_ptr, prc_ptr, thrd_ptr, Tracked(process_lock_perm), Tracked(thread_lock_perm)),
        PageSize::SZ1g => thread_exit_return_quota_1g(krnl, Tracked(&mut *lctx), ctn_ptr, prc_ptr, thrd_ptr, Tracked(process_lock_perm), Tracked(thread_lock_perm)),
    }
}
} // verus!
