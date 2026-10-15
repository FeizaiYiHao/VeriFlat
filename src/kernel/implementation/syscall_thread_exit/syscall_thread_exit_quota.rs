use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_quota_spec::thread_exit_quota_transition;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_quota_eof::thread_exit_quota_eof;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_destroy_eof::thread_exit_quota_sums_bounded;

verus! {
/// Return the whole `size` quota of the running last thread `thread_ptr` and of its process `process_ptr` to the `size`
/// allocator of their container `container_ptr` under that allocator's quota lock, and record the return as the thread's
/// progress.
pub(super) fn thread_exit_return_quota(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
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
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        kernel_thread_exit_quota_returned(old(krnl), final(krnl), thread_ptr, size),
        *final(krnl) == (KernelK {
            prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp,
            ..*old(krnl)
        }),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr).view() == match size {
            PageSize::SZ4k => Process { quota_4k: 0, ..old(krnl).prc_mp.spec_index(process_ptr).view() },
            PageSize::SZ2m => Process { quota_2m: 0, ..old(krnl).prc_mp.spec_index(process_ptr).view() },
            PageSize::SZ1g => Process { quota_1g: 0, ..old(krnl).prc_mp.spec_index(process_ptr).view() },
        },
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata() == old(krnl).prc_mp.spec_index(process_ptr).view_rodata(),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost() == old(krnl).prc_mp.spec_index(process_ptr).view_ghost(),
        final(krnl).prc_mp.spec_index(process_ptr).locking_thread() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread(),
        final(krnl).prc_mp.spec_index(process_ptr).being_killed() == old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == match size {
            PageSize::SZ4k => Thread { quota_4k: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: size })), ..old(krnl).thr_mp.spec_index(thread_ptr).view() },
            PageSize::SZ2m => Thread { quota_2m: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: size })), ..old(krnl).thr_mp.spec_index(thread_ptr).view() },
            PageSize::SZ1g => Thread { quota_1g: 0, syscall_progress: Ghost(Some(SyscallProgress::ThreadExitQuota { returned: size })), ..old(krnl).thr_mp.spec_index(thread_ptr).view() },
        },
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
{
    proof {
        thread_exit_quota_sums_bounded(&*krnl, container_ptr, process_ptr, thread_ptr);
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
    }
    match size {
        PageSize::SZ4k => {
            let allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
            proof { assert(krnl.allc_4k_mp.dom().contains(allocator_ptr) && krnl.allc_4k_mp.spec_index(allocator_ptr).wf()) by {
                container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
            }; }
            let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
            let ghost locked = *krnl;
            proof {
                process_perms_wf_at(krnl.prc_mp, process_ptr); thread_perms_wf_at(krnl.thr_mp, thread_ptr);
                assert(krnl.allc_4k_mp.perms_wf()) by { allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr); };
            }
            let process_quota = {
                let process = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm));
                let quota = process.quota_4k;
                process.quota_4k = 0;
                quota
            };
            let thread_quota = {
                let thread = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
                let quota = thread.quota_4k;
                thread.quota_4k = 0;
                quota
            };
            {
                let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
                    Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
                quota.value = quota.value + process_quota + thread_quota;
            }
            proof {
                assert(thread_exit_quota_transition(locked, *krnl, process_ptr, thread_ptr, allocator_ptr, size)) by { reveal(thread_exit_quota_transition); };
                thread_exit_quota_eof(locked, *krnl, container_ptr, process_ptr, thread_ptr, allocator_ptr, size);
                assert(krnl.allc_4k_mp.spec_index(allocator_ptr).wf() && krnl.allc_4k_mp.spec_index(allocator_ptr).quota.inv()) by { allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr); };
            }
            krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_lock_perm));
            proof { assert(lctx.allocator_quota_4k_lock_map() =~= old(lctx).allocator_quota_4k_lock_map()); }
        }
        PageSize::SZ2m => {
            let allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_2m;
            proof { assert(krnl.allc_2m_mp.dom().contains(allocator_ptr) && krnl.allc_2m_mp.spec_index(allocator_ptr).wf()) by {
                container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); allocator_perms_wf_at(krnl.allc_2m_mp, allocator_ptr);
            }; }
            let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_2m(allocator_ptr, Tracked(&mut *lctx));
            let ghost locked = *krnl;
            proof {
                process_perms_wf_at(krnl.prc_mp, process_ptr); thread_perms_wf_at(krnl.thr_mp, thread_ptr);
                assert(krnl.allc_2m_mp.perms_wf()) by { allocator_perms_wf_at(krnl.allc_2m_mp, allocator_ptr); };
            }
            let process_quota = {
                let process = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm));
                let quota = process.quota_2m;
                process.quota_2m = 0;
                quota
            };
            let thread_quota = {
                let thread = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
                let quota = thread.quota_2m;
                thread.quota_2m = 0;
                quota
            };
            {
                let quota = krnl.allc_2m_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()),
                    Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
                quota.value = quota.value + process_quota + thread_quota;
            }
            proof {
                assert(thread_exit_quota_transition(locked, *krnl, process_ptr, thread_ptr, allocator_ptr, size)) by { reveal(thread_exit_quota_transition); };
                thread_exit_quota_eof(locked, *krnl, container_ptr, process_ptr, thread_ptr, allocator_ptr, size);
                assert(krnl.allc_2m_mp.spec_index(allocator_ptr).wf() && krnl.allc_2m_mp.spec_index(allocator_ptr).quota.inv()) by { allocator_perms_wf_at(krnl.allc_2m_mp, allocator_ptr); };
            }
            krnl.wunlock_allocator_quota_2m(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_lock_perm));
            proof { assert(lctx.allocator_quota_2m_lock_map() =~= old(lctx).allocator_quota_2m_lock_map()); }
        }
        PageSize::SZ1g => {
            let allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_1g;
            proof { assert(krnl.allc_1g_mp.dom().contains(allocator_ptr) && krnl.allc_1g_mp.spec_index(allocator_ptr).wf()) by {
                container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); allocator_perms_wf_at(krnl.allc_1g_mp, allocator_ptr);
            }; }
            let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_1g(allocator_ptr, Tracked(&mut *lctx));
            let ghost locked = *krnl;
            proof {
                process_perms_wf_at(krnl.prc_mp, process_ptr); thread_perms_wf_at(krnl.thr_mp, thread_ptr);
                assert(krnl.allc_1g_mp.perms_wf()) by { allocator_perms_wf_at(krnl.allc_1g_mp, allocator_ptr); };
            }
            let process_quota = {
                let process = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm));
                let quota = process.quota_1g;
                process.quota_1g = 0;
                quota
            };
            let thread_quota = {
                let thread = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
                let quota = thread.quota_1g;
                thread.quota_1g = 0;
                quota
            };
            {
                let quota = krnl.allc_1g_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_1g_lock_map()), Ghost(lctx.allocator_cache_1g_lock_map()),
                    Ghost(lctx.allocator_global_pool_1g_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
                quota.value = quota.value + process_quota + thread_quota;
            }
            proof {
                assert(thread_exit_quota_transition(locked, *krnl, process_ptr, thread_ptr, allocator_ptr, size)) by { reveal(thread_exit_quota_transition); };
                thread_exit_quota_eof(locked, *krnl, container_ptr, process_ptr, thread_ptr, allocator_ptr, size);
                assert(krnl.allc_1g_mp.spec_index(allocator_ptr).wf() && krnl.allc_1g_mp.spec_index(allocator_ptr).quota.inv()) by { allocator_perms_wf_at(krnl.allc_1g_mp, allocator_ptr); };
            }
            krnl.wunlock_allocator_quota_1g(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_lock_perm));
            proof { assert(lctx.allocator_quota_1g_lock_map() =~= old(lctx).allocator_quota_1g_lock_map()); }
        }
    }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::ThreadExitQuota { returned: size })), Tracked(&*lctx), Tracked(thread_lock_perm));
    proof { assert(kernel_thread_exit_quota_returned(old(krnl), &*krnl, thread_ptr, size)) by { reveal(kernel_thread_exit_quota_returned); reveal(container_allocator_wf); }; }
}
} // verus!
