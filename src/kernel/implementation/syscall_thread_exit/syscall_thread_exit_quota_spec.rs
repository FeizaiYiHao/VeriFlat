use vstd::prelude::*;
use crate::*;

verus! {
/// The write-held allocator `allc_ptr` regains `returned` quota; nothing else in its map changes.
pub(super) open spec fn thread_exit_quota_eof_allocator_returned<const SIZE: usize>(pre_allocators: PageAllocatorUnLockedMap<SIZE>, post_allocators: PageAllocatorUnLockedMap<SIZE>, allc_ptr: RwLockPageAllocatorPtr, returned: int) -> bool {
    let allocator = pre_allocators.spec_index(allc_ptr);
    &&& post_allocators.perms_wf()
    &&& post_allocators.unchanged_except(&pre_allocators, allc_ptr)
    &&& post_allocators.spec_index(allc_ptr).quota.view() == (AllocatorQuota { value: (allocator.quota.view().value + returned) as usize, ..allocator.quota.view() })
    &&& post_allocators.spec_index(allc_ptr).quota.is_init()
    &&& post_allocators.spec_index(allc_ptr).quota.view_rodata() == allocator.quota.view_rodata()
    &&& post_allocators.spec_index(allc_ptr).quota.view_ghost() == allocator.quota.view_ghost()
    &&& post_allocators.spec_index(allc_ptr).quota.locking_thread() == allocator.quota.locking_thread()
    &&& post_allocators.spec_index(allc_ptr).quota.being_killed() == allocator.quota.being_killed()
    &&& post_allocators.spec_index(allc_ptr).cpu_caches == allocator.cpu_caches
    &&& post_allocators.spec_index(allc_ptr).global_pool == allocator.global_pool
    &&& post_allocators.spec_index(allc_ptr).owning_container == allocator.owning_container
    &&& post_allocators.spec_index(allc_ptr).total_free_pages == allocator.total_free_pages
}

/// Returning the `size` quota of the exiting thread `thrd_ptr` and of its process `prc_ptr`: both drop their
/// whole `size` quota, which the write-held `size` allocator `allc_ptr` of their container regains. Lock owners,
/// lock ids, and every other object stay.
#[verifier::opaque]
pub(super) open spec fn thread_exit_quota_eof_transition_framing(
    pre: KernelK, post: KernelK, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, allc_ptr: RwLockPageAllocatorPtr, size: PageSize,
) -> bool {
    let process = pre.prc_mp.spec_index(prc_ptr);
    let thread = pre.thrd_mp.spec_index(thrd_ptr);
    let returned = match size {
        PageSize::SZ4k => process.view().quota_4k + thread.view().quota_4k,
        PageSize::SZ2m => process.view().quota_2m + thread.view().quota_2m,
        PageSize::SZ1g => process.view().quota_1g + thread.view().quota_1g,
    };
    &&& post == (KernelK { prc_mp: post.prc_mp, thrd_mp: post.thrd_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, ..pre })
    &&& !(size is SZ4k) ==> post.allc_4k_mp == pre.allc_4k_mp
    &&& !(size is SZ2m) ==> post.allc_2m_mp == pre.allc_2m_mp
    &&& !(size is SZ1g) ==> post.allc_1g_mp == pre.allc_1g_mp
    &&& size is SZ4k ==> thread_exit_quota_eof_allocator_returned(pre.allc_4k_mp, post.allc_4k_mp, allc_ptr, returned)
    &&& size is SZ2m ==> thread_exit_quota_eof_allocator_returned(pre.allc_2m_mp, post.allc_2m_mp, allc_ptr, returned)
    &&& size is SZ1g ==> thread_exit_quota_eof_allocator_returned(pre.allc_1g_mp, post.allc_1g_mp, allc_ptr, returned)
    &&& post.prc_mp.perms_wf()
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, prc_ptr)
    &&& post.prc_mp.spec_index(prc_ptr).is_init()
    &&& post.prc_mp.spec_index(prc_ptr).view() == match size {
        PageSize::SZ4k => Process { quota_4k: 0, ..process.view() },
        PageSize::SZ2m => Process { quota_2m: 0, ..process.view() },
        PageSize::SZ1g => Process { quota_1g: 0, ..process.view() },
    }
    &&& post.prc_mp.spec_index(prc_ptr).view_rodata() == process.view_rodata()
    &&& post.prc_mp.spec_index(prc_ptr).view_ghost() == process.view_ghost()
    &&& post.prc_mp.spec_index(prc_ptr).locking_thread() == process.locking_thread()
    &&& post.prc_mp.spec_index(prc_ptr).being_killed() == process.being_killed()
    &&& post.thrd_mp.perms_wf()
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr)
    &&& post.thrd_mp.spec_index(thrd_ptr).is_init()
    &&& post.thrd_mp.spec_index(thrd_ptr).view() == match size {
        PageSize::SZ4k => Thread { quota_4k: 0, ..thread.view() },
        PageSize::SZ2m => Thread { quota_2m: 0, ..thread.view() },
        PageSize::SZ1g => Thread { quota_1g: 0, ..thread.view() },
    }
    &&& post.thrd_mp.spec_index(thrd_ptr).locking_thread() == thread.locking_thread()
    &&& post.thrd_mp.spec_index(thrd_ptr).view_ghost() == thread.view_ghost()
    &&& post.thrd_mp.spec_index(thrd_ptr).being_killed() == thread.being_killed() && post.thrd_mp.spec_index(thrd_ptr).killer_info() == thread.killer_info()
}
} // verus!
