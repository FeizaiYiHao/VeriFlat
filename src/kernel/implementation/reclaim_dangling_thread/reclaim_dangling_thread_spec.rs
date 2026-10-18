use vstd::prelude::*;
use crate::*;

verus! {
/// The killed dangling thread `dangling_ptr`, which no process or other thread refers to and which holds no quota, leaves the thread
/// map and the thread sets of its container and that container's ancestors, and its page returns through its free-list
/// node at `cache_node_addr` to shard `cpu_id` of the 4K allocator `allocator_ptr` of its owner `owner`, whose quota
/// grows by one.
#[verifier::opaque]
pub open spec fn reclaim_dangling_thread_transition(
    pre: KernelK, post: KernelK, cpu_id: CpuId, dangling_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, cache_node_addr: usize,
) -> bool {
    let page_index = page_ptr2page_index(dangling_ptr);
    let dangling = pre.thr_mp.spec_index(dangling_ptr).view();
    let pre_page = pre.pg_arr.spec_index(page_index).view();
    let post_page = post.pg_arr.spec_index(page_index).view();
    let free_state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } };
    let pre_allocator = pre.allc_4k_mp.spec_index(allocator_ptr);
    let post_allocator = post.allc_4k_mp.spec_index(allocator_ptr);
    let pre_cache = pre_allocator.cpu_caches.spec_index(cpu_id).view();
    let post_cache = post_allocator.cpu_caches.spec_index(cpu_id).view();
    let container_ptr = dangling.owning_container;
    let uppers = pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& page_ptr_valid(dangling_ptr)
    &&& pre.thr_mp.dom().contains(dangling_ptr)
    &&& pre.thr_mp.spec_index(dangling_ptr).locking_thread() is Write
    &&& dangling.state is KILLED
    &&& dangling.proc_linkedlist_node.is_init()
    &&& dangling.caller is None
    &&& dangling.callee is None
    &&& forall|j: int| #![trigger dangling.endpoint_descriptors.view().spec_index(j)] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> dangling.endpoint_descriptors.view().spec_index(j) is None
    &&& dangling.temp_alloc_clean()
    &&& dangling.quota_4k == 0
    &&& dangling.quota_2m == 0
    &&& dangling.quota_1g == 0
    &&& dangling.free_quota_pending_clean()
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& pre.ctn_mp.dom().contains(owner)
    &&& pre_page.view().owning_container == owner
    &&& pre_page.view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread })
    &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
    &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
    &&& post == (KernelK { ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let before = pre.ctn_mp.spec_index(c);
            let after = post.ctn_mp.spec_index(c);
            &&& after.view() == before.view()
            &&& after.view_rodata() == before.view_rodata()
            &&& after.locking_thread() == before.locking_thread()
            &&& after.being_killed() == before.being_killed()
            &&& after.view_ghost() == (ContainerGhost {
                owned_threads: if c == container_ptr { Ghost(before.view_ghost().owned_threads.view().remove(dangling_ptr)) } else { before.view_ghost().owned_threads },
                owned_indirect_threads: if uppers.to_set().contains(c) { Ghost(before.view_ghost().owned_indirect_threads.view().remove(dangling_ptr)) }
                    else { before.view_ghost().owned_indirect_threads },
                ..before.view_ghost()
            })
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom().remove(dangling_ptr)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] post.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t) == pre.thr_mp.spec_index(t)
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& forall|i: PageIndex| #![trigger pre.pg_arr.spec_index(i).view().view().state] #![trigger post.pg_arr.spec_index(i).view().view().state]
        index_valid(NUM_PAGES, i) ==> {
            &&& post.pg_arr.spec_index(i).view().view().state == if i == page_index { free_state } else { pre.pg_arr.spec_index(i).view().view().state }
            &&& post.pg_arr.spec_index(i).view().view().owning_container == pre.pg_arr.spec_index(i).view().view().owning_container
            &&& post.pg_arr.spec_index(i).view().view().mappings() == pre.pg_arr.spec_index(i).view().view().mappings()
        }
    &&& post_page.is_init() == pre_page.is_init()
    &&& post_page.view_rodata() == pre_page.view_rodata()
    &&& post_page.view_ghost() == pre_page.view_ghost()
    &&& post_page.locking_thread() == pre_page.locking_thread()
    &&& post_page.being_killed() == pre_page.being_killed()
    &&& pre_page.view().free_list_node_storage.addr() == cache_node_addr
    &&& post_page.view().free_list_node_storage.addr() == cache_node_addr
    &&& post_page.view() == (Page { state: free_state, free_list_node_storage: post_page.view().free_list_node_storage, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr)
    &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + 1
    &&& post_cache.view().view() == pre_cache.view().view().insert(0, dangling_ptr)
    &&& post_cache.view().map() == pre_cache.view().map().insert(cache_node_addr, dangling_ptr)
    &&& !pre_cache.view().map().dom().contains(cache_node_addr)
    &&& post_allocator.cpu_caches.entries_unchanged_except(&pre_allocator.cpu_caches, cpu_id)
    &&& post_cache.locking_thread() == pre_cache.locking_thread()
    &&& post_allocator.global_pool == pre_allocator.global_pool
    &&& post_allocator.owning_container == pre_allocator.owning_container
    &&& post_allocator.quota.view().value == pre_allocator.quota.view().value + 1
    &&& post_allocator.quota.view() == (AllocatorQuota { value: post_allocator.quota.view().value, ..pre_allocator.quota.view() })
    &&& post_allocator.quota.is_init() == pre_allocator.quota.is_init()
    &&& post_allocator.quota.view_rodata() == pre_allocator.quota.view_rodata()
    &&& post_allocator.quota.view_ghost() == pre_allocator.quota.view_ghost()
    &&& post_allocator.quota.locking_thread() == pre_allocator.quota.locking_thread()
    &&& post_allocator.quota.being_killed() == pre_allocator.quota.being_killed()
}
} // verus!
