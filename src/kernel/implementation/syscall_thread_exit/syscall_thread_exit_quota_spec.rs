use vstd::prelude::*;
use crate::*;

verus! {
/// Returning the `size` quota of the exiting thread `thread_ptr` and of its process `process_ptr`: both drop their whole
/// `size` quota, which the write-held `size` allocator `allocator_ptr` of their container regains. Lock owners, lock ids,
/// and every other object stay.
#[verifier::opaque]
pub open spec fn thread_exit_quota_transition(
    pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, allocator_ptr: RwLockPageAllocatorPtr, size: PageSize,
) -> bool {
    let process = pre.prc_mp.spec_index(process_ptr);
    let thread = pre.thr_mp.spec_index(thread_ptr);
    let pre_allocators = match size { PageSize::SZ4k => pre.allc_4k_mp, PageSize::SZ2m => pre.allc_2m_mp, PageSize::SZ1g => pre.allc_1g_mp };
    let post_allocators = match size { PageSize::SZ4k => post.allc_4k_mp, PageSize::SZ2m => post.allc_2m_mp, PageSize::SZ1g => post.allc_1g_mp };
    let allocator = pre_allocators.spec_index(allocator_ptr);
    let returned = match size {
        PageSize::SZ4k => process.view().quota_4k + thread.view().quota_4k,
        PageSize::SZ2m => process.view().quota_2m + thread.view().quota_2m,
        PageSize::SZ1g => process.view().quota_1g + thread.view().quota_1g,
    };
    &&& post == (KernelK { prc_mp: post.prc_mp, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, ..pre })
    &&& !(size is SZ4k) ==> post.allc_4k_mp == pre.allc_4k_mp
    &&& !(size is SZ2m) ==> post.allc_2m_mp == pre.allc_2m_mp
    &&& !(size is SZ1g) ==> post.allc_1g_mp == pre.allc_1g_mp
    &&& post_allocators.perms_wf()
    &&& post_allocators.unchanged_except(&pre_allocators, allocator_ptr)
    &&& post_allocators.spec_index(allocator_ptr).quota.view() == (AllocatorQuota { value: (allocator.quota.view().value + returned) as usize, ..allocator.quota.view() })
    &&& post_allocators.spec_index(allocator_ptr).quota.is_init()
    &&& post_allocators.spec_index(allocator_ptr).quota.view_rodata() == allocator.quota.view_rodata()
    &&& post_allocators.spec_index(allocator_ptr).quota.view_ghost() == allocator.quota.view_ghost()
    &&& post_allocators.spec_index(allocator_ptr).quota.locking_thread() == allocator.quota.locking_thread()
    &&& post_allocators.spec_index(allocator_ptr).quota.being_killed() == allocator.quota.being_killed()
    &&& post_allocators.spec_index(allocator_ptr).cpu_caches == allocator.cpu_caches
    &&& post_allocators.spec_index(allocator_ptr).global_pool == allocator.global_pool
    &&& post_allocators.spec_index(allocator_ptr).owning_container == allocator.owning_container
    &&& post_allocators.spec_index(allocator_ptr).total_free_pages == allocator.total_free_pages
    &&& post.prc_mp.perms_wf()
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& post.prc_mp.spec_index(process_ptr).is_init()
    &&& post.prc_mp.spec_index(process_ptr).view() == match size {
        PageSize::SZ4k => Process { quota_4k: 0, ..process.view() },
        PageSize::SZ2m => Process { quota_2m: 0, ..process.view() },
        PageSize::SZ1g => Process { quota_1g: 0, ..process.view() },
    }
    &&& post.prc_mp.spec_index(process_ptr).view_rodata() == process.view_rodata()
    &&& post.prc_mp.spec_index(process_ptr).view_ghost() == process.view_ghost()
    &&& post.prc_mp.spec_index(process_ptr).locking_thread() == process.locking_thread()
    &&& post.prc_mp.spec_index(process_ptr).being_killed() == process.being_killed()
    &&& post.thr_mp.perms_wf()
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& post.thr_mp.spec_index(thread_ptr).is_init()
    &&& post.thr_mp.spec_index(thread_ptr).view() == match size {
        PageSize::SZ4k => Thread { quota_4k: 0, ..thread.view() },
        PageSize::SZ2m => Thread { quota_2m: 0, ..thread.view() },
        PageSize::SZ1g => Thread { quota_1g: 0, ..thread.view() },
    }
    &&& post.thr_mp.spec_index(thread_ptr).locking_thread() == thread.locking_thread()
    &&& post.thr_mp.spec_index(thread_ptr).being_killed() == thread.being_killed()
}
} // verus!
