use vstd::prelude::*;
use crate::*;

verus! {
/// Descriptor `index` of `thread_ptr`, the last reference to the endpoint `endpoint_ptr`, is cleared; the endpoint leaves the
/// endpoint map and its owner's endpoint set, its page returns through its free-list node at `node_addr` to the global pool
/// of the 4K allocator `allocator_ptr` of the page's owner, and that allocator's quota grows by one.
#[verifier::opaque]
pub open spec fn release_endpoint_eof_transition_framing(
    pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx, allocator_ptr: RwLockPageAllocatorPtr, node_addr: usize,
) -> bool {
    let page_index = page_ptr2page_index(endpoint_ptr);
    let old_thread = pre.thr_mp.spec_index(thread_ptr);
    let new_thread = post.thr_mp.spec_index(thread_ptr);
    let endpoint_owner = pre.ep_mp.spec_index(endpoint_ptr).view().owning_container;
    let pre_page = pre.pg_arr.spec_index(page_index).view();
    let post_page = post.pg_arr.spec_index(page_index).view();
    let free_state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::GlobalList };
    let pre_allocator = pre.allc_4k_mp.spec_index(allocator_ptr);
    let post_allocator = post.allc_4k_mp.spec_index(allocator_ptr);
    &&& post == (KernelK { ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, ep_mp: post.ep_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& new_thread.is_init()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.view() == (Thread { endpoint_descriptors: new_thread.view().endpoint_descriptors, ..old_thread.view() })
    &&& new_thread.view().endpoint_descriptors.view() == old_thread.view().endpoint_descriptors.view().update(index as int, None)
    &&& post.ep_mp.dom() == pre.ep_mp.dom().remove(endpoint_ptr)
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)] post.ep_mp.dom().contains(e) ==> post.ep_mp.spec_index(e) == pre.ep_mp.spec_index(e)
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let a = pre.ctn_mp.spec_index(c);
            let b = post.ctn_mp.spec_index(c);
            &&& b.view() == a.view()
            &&& b.view_rodata() == a.view_rodata()
            &&& b.locking_thread() == a.locking_thread()
            &&& b.killer_info() == a.killer_info()
            &&& b.control() == a.control()
            &&& b.view_ghost() == if c == endpoint_owner { ContainerGhost { owned_endpoints: Ghost(a.view_ghost().owned_endpoints.view().remove(endpoint_ptr)), ..a.view_ghost() } } else { a.view_ghost() }
        }
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
    &&& post_page.view().free_list_node_storage.addr() == node_addr
    &&& post_page.view() == (Page { state: free_state, free_list_node_storage: post_page.view().free_list_node_storage, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr)
    &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + 1
    &&& !pre_allocator.global_pool.view().map().dom().contains(node_addr)
    &&& post_allocator.global_pool.view().view() == pre_allocator.global_pool.view().view().insert(0, endpoint_ptr)
    &&& post_allocator.global_pool.view().map() == pre_allocator.global_pool.view().map().insert(node_addr, endpoint_ptr)
    &&& post_allocator.global_pool.is_init()
    &&& post_allocator.global_pool.lock_id() == pre_allocator.global_pool.lock_id()
    &&& post_allocator.global_pool.locking_thread() == pre_allocator.global_pool.locking_thread()
    &&& post_allocator.global_pool.being_killed() == pre_allocator.global_pool.being_killed()
    &&& post_allocator.cpu_caches == pre_allocator.cpu_caches
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
