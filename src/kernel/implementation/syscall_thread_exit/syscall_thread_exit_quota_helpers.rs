use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_quota_spec::thread_exit_quota_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_quota_eof::thread_exit_quota_eof;

verus! {
/// Return the whole 4K quota of the running last thread `thrd_ptr` and of its process `prc_ptr` to the 4K
/// allocator of their container `ctn_ptr` under that allocator's quota lock, and record the return as the
/// thread's progress.
pub(super) fn thread_exit_return_quota_4k(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
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
        kernel_thread_exit_quota_returned(old(krnl), final(krnl), thrd_ptr, PageSize::SZ4k),
        *final(krnl) == (KernelK {
            prc_mp: final(krnl).prc_mp, thrd_mp: final(krnl).thrd_mp, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp,
            ..*old(krnl)
        }),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, prc_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr).view() == (Process { quota_4k: 0, ..old(krnl).prc_mp.spec_index(prc_ptr).view() }),
        final(krnl).prc_mp.spec_index(prc_ptr).view_rodata() == old(krnl).prc_mp.spec_index(prc_ptr).view_rodata(),
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost() == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost(),
        final(krnl).prc_mp.spec_index(prc_ptr).locking_thread() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread(),
        final(krnl).prc_mp.spec_index(prc_ptr).being_killed() == old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        final(krnl).thrd_mp.dom() == old(krnl).thrd_mp.dom(),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { quota_4k: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ4k })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
{
    proof {
        container_process_thread_quota_sums_bounded(&*krnl, ctn_ptr, prc_ptr, thrd_ptr);
        container_perms_wf_at(krnl.ctn_mp, ctn_ptr);
    }
    let allc_ptr = krnl.ctn_mp.borrow_rodata(ctn_ptr).borrow().allocator_ptr_4k;
    proof { assert(krnl.allc_4k_mp.dom().contains(allc_ptr)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr); }; }
    let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_4k(allc_ptr, Tracked(&mut *lctx));
    let ghost locked = *krnl;
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, prc_ptr); thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); }
    let process_quota = {
        let process = krnl.prc_mp.borrow_mut_typed(prc_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm));
        let quota = process.quota_4k;
        process.quota_4k = 0;
        quota
    };
    let thread_quota = {
        let thread = krnl.thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
        let quota = thread.quota_4k;
        thread.quota_4k = 0;
        quota
    };
    let allocator_quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allc_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
    allocator_quota.value = allocator_quota.value + process_quota + thread_quota;
    proof {
        assert(thread_exit_quota_eof_transition_framing(locked, *krnl, prc_ptr, thrd_ptr, allc_ptr, PageSize::SZ4k)) by { reveal(thread_exit_quota_eof_transition_framing); };
        thread_exit_quota_eof(locked, *krnl, ctn_ptr, prc_ptr, thrd_ptr, allc_ptr, PageSize::SZ4k);
    }
    krnl.wunlock_allocator_quota_4k(allc_ptr, Tracked(&mut *lctx), Tracked(quota_lock_perm));
    proof { assert(lctx.allocator_quota_4k_lock_map() =~= old(lctx).allocator_quota_4k_lock_map()); }
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ4k })), Tracked(&*lctx), Tracked(thread_lock_perm));
    proof { assert(kernel_thread_exit_quota_returned(old(krnl), &*krnl, thrd_ptr, PageSize::SZ4k)) by { reveal(kernel_thread_exit_quota_returned); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }; }
}

/// Return the whole 2M quota of the running last thread `thrd_ptr` and of its process `prc_ptr` to the 2M
/// allocator of their container `ctn_ptr` under that allocator's quota lock, and record the return as the
/// thread's progress.
pub(super) fn thread_exit_return_quota_2m(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
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
        kernel_thread_exit_quota_returned(old(krnl), final(krnl), thrd_ptr, PageSize::SZ2m),
        *final(krnl) == (KernelK {
            prc_mp: final(krnl).prc_mp, thrd_mp: final(krnl).thrd_mp, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp,
            ..*old(krnl)
        }),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, prc_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr).view() == (Process { quota_2m: 0, ..old(krnl).prc_mp.spec_index(prc_ptr).view() }),
        final(krnl).prc_mp.spec_index(prc_ptr).view_rodata() == old(krnl).prc_mp.spec_index(prc_ptr).view_rodata(),
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost() == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost(),
        final(krnl).prc_mp.spec_index(prc_ptr).locking_thread() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread(),
        final(krnl).prc_mp.spec_index(prc_ptr).being_killed() == old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        final(krnl).thrd_mp.dom() == old(krnl).thrd_mp.dom(),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { quota_2m: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ2m })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
{
    proof {
        container_process_thread_quota_sums_bounded(&*krnl, ctn_ptr, prc_ptr, thrd_ptr);
        container_perms_wf_at(krnl.ctn_mp, ctn_ptr);
    }
    let allc_ptr = krnl.ctn_mp.borrow_rodata(ctn_ptr).borrow().allocator_ptr_2m;
    proof { assert(krnl.allc_2m_mp.dom().contains(allc_ptr)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr); }; }
    let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_2m(allc_ptr, Tracked(&mut *lctx));
    let ghost locked = *krnl;
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, prc_ptr); thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); }
    let process_quota = {
        let process = krnl.prc_mp.borrow_mut_typed(prc_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm));
        let quota = process.quota_2m;
        process.quota_2m = 0;
        quota
    };
    let thread_quota = {
        let thread = krnl.thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
        let quota = thread.quota_2m;
        thread.quota_2m = 0;
        quota
    };
    let allocator_quota = krnl.allc_2m_mp.borrow_mut_quota_typed(allc_ptr, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()),
        Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
    allocator_quota.value = allocator_quota.value + process_quota + thread_quota;
    proof {
        assert(thread_exit_quota_eof_transition_framing(locked, *krnl, prc_ptr, thrd_ptr, allc_ptr, PageSize::SZ2m)) by { reveal(thread_exit_quota_eof_transition_framing); };
        thread_exit_quota_eof(locked, *krnl, ctn_ptr, prc_ptr, thrd_ptr, allc_ptr, PageSize::SZ2m);
    }
    krnl.wunlock_allocator_quota_2m(allc_ptr, Tracked(&mut *lctx), Tracked(quota_lock_perm));
    proof { assert(lctx.allocator_quota_2m_lock_map() =~= old(lctx).allocator_quota_2m_lock_map()); }
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ2m })), Tracked(&*lctx), Tracked(thread_lock_perm));
    proof { assert(kernel_thread_exit_quota_returned(old(krnl), &*krnl, thrd_ptr, PageSize::SZ2m)) by { reveal(kernel_thread_exit_quota_returned); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }; }
}

/// Return the whole 1G quota of the running last thread `thrd_ptr` and of its process `prc_ptr` to the 1G
/// allocator of their container `ctn_ptr` under that allocator's quota lock, and record the return as the
/// thread's progress.
pub(super) fn thread_exit_return_quota_1g(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    Tracked(process_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
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
        kernel_thread_exit_quota_returned(old(krnl), final(krnl), thrd_ptr, PageSize::SZ1g),
        *final(krnl) == (KernelK {
            prc_mp: final(krnl).prc_mp, thrd_mp: final(krnl).thrd_mp, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp,
            ..*old(krnl)
        }),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, prc_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr).view() == (Process { quota_1g: 0, ..old(krnl).prc_mp.spec_index(prc_ptr).view() }),
        final(krnl).prc_mp.spec_index(prc_ptr).view_rodata() == old(krnl).prc_mp.spec_index(prc_ptr).view_rodata(),
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost() == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost(),
        final(krnl).prc_mp.spec_index(prc_ptr).locking_thread() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread(),
        final(krnl).prc_mp.spec_index(prc_ptr).being_killed() == old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        final(krnl).thrd_mp.dom() == old(krnl).thrd_mp.dom(),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { quota_1g: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ1g })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
{
    proof {
        container_process_thread_quota_sums_bounded(&*krnl, ctn_ptr, prc_ptr, thrd_ptr);
        container_perms_wf_at(krnl.ctn_mp, ctn_ptr);
    }
    let allc_ptr = krnl.ctn_mp.borrow_rodata(ctn_ptr).borrow().allocator_ptr_1g;
    proof { assert(krnl.allc_1g_mp.dom().contains(allc_ptr)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr); }; }
    let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_1g(allc_ptr, Tracked(&mut *lctx));
    let ghost locked = *krnl;
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, prc_ptr); thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); }
    let process_quota = {
        let process = krnl.prc_mp.borrow_mut_typed(prc_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm));
        let quota = process.quota_1g;
        process.quota_1g = 0;
        quota
    };
    let thread_quota = {
        let thread = krnl.thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
        let quota = thread.quota_1g;
        thread.quota_1g = 0;
        quota
    };
    let allocator_quota = krnl.allc_1g_mp.borrow_mut_quota_typed(allc_ptr, Ghost(lctx.allocator_quota_1g_lock_map()), Ghost(lctx.allocator_cache_1g_lock_map()),
        Ghost(lctx.allocator_global_pool_1g_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
    allocator_quota.value = allocator_quota.value + process_quota + thread_quota;
    proof {
        assert(thread_exit_quota_eof_transition_framing(locked, *krnl, prc_ptr, thrd_ptr, allc_ptr, PageSize::SZ1g)) by { reveal(thread_exit_quota_eof_transition_framing); };
        thread_exit_quota_eof(locked, *krnl, ctn_ptr, prc_ptr, thrd_ptr, allc_ptr, PageSize::SZ1g);
    }
    krnl.wunlock_allocator_quota_1g(allc_ptr, Tracked(&mut *lctx), Tracked(quota_lock_perm));
    proof { assert(lctx.allocator_quota_1g_lock_map() =~= old(lctx).allocator_quota_1g_lock_map()); }
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ1g })), Tracked(&*lctx), Tracked(thread_lock_perm));
    proof { assert(kernel_thread_exit_quota_returned(old(krnl), &*krnl, thrd_ptr, PageSize::SZ1g)) by { reveal(kernel_thread_exit_quota_returned); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); }; }
}
} // verus!
