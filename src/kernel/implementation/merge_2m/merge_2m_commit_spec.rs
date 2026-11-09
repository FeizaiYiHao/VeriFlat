#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scan::*;

verus! {
pub open spec fn merge_2m_exchange_thread_quotas_eof_transition_framing(pre: Thread, post: Thread) -> bool {
    post == (Thread { quota_4k: (pre.quota_4k - 512) as usize, quota_2m: (pre.quota_2m + 1) as usize, ..pre })
}

pub open spec fn merge_2m_commit_eof_transition_framing(pre: KernelK, post: KernelK,
    thread: RwLockThreadPtr, allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr,
    candidate: Merge2mCandidate) -> bool {
    let head = candidate.head;
    let head_ptr = spec_page_index2page_ptr(head);
    let head_node = pre.pg_arr.spec_index(head).view().view().free_list_node_storage.addr();
    let region = Set::<PageIndex>::range(head, (head + 512) as usize);
    let removed = |source: usize, pointer: PagePtr| region.contains(spec_page_ptr2page_index(pointer))
        && pointer == spec_page_index2page_ptr(spec_page_ptr2page_index(pointer)) && candidate.sources.view().spec_index(spec_page_ptr2page_index(pointer) as int - head as int) as usize == source;
    &&& post.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(NUM_CPUS) == post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list
    &&& pre.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(NUM_CPUS) == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list
    &&& post == (KernelK { pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, ..pre })
    &&& forall|index: PageIndex| #![trigger post.pg_arr.spec_index(index)] #![trigger pre.pg_arr.spec_index(index)]
        index_valid(NUM_PAGES, index) && !region.contains(index) ==> post.pg_arr.spec_index(index) == pre.pg_arr.spec_index(index)
    &&& forall|index: PageIndex| #![trigger post.pg_arr.spec_index(index)]
        #![trigger pre.ctn_mp.spec_index(pre.pg_arr.spec_index(head).view().view().owning_container).view().owned_pages.view().contains(spec_page_index2page_ptr(index))]
        region.contains(index) ==> {
        let old_cell = pre.pg_arr.spec_index(index).view();
        let new_cell = post.pg_arr.spec_index(index).view();
        let old_page = old_cell.view();
        let new_page = new_cell.view();
        &&& new_cell.is_init() == old_cell.is_init()
        &&& new_cell.locking_thread() == old_cell.locking_thread()
        &&& new_cell.being_killed() == old_cell.being_killed()
        &&& new_cell.view_rodata() == old_cell.view_rodata()
        &&& new_cell.view_ghost() == old_cell.view_ghost()
        &&& new_cell.control() == old_cell.control()
        &&& new_cell.killer_info() == old_cell.killer_info()
        &&& post.pg_arr.lock_id_by_index(index) == pre.pg_arr.lock_id_by_index(index)
        &&& new_page == (Page { state: new_page.state, perm_4k: new_page.perm_4k,
            perm_2m: new_page.perm_2m, free_list_node_storage: new_page.free_list_node_storage, ..old_page })
        &&& new_page.perm_4k.view().is_none()
        &&& new_page.free_list_node_storage.addr() == old_page.free_list_node_storage.addr()
        &&& old_page.owning_container == pre.allc_4k_mp.spec_index(allocator_4k).owning_container
        &&& if index == head {
            &&& new_page.state == PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state: FreePageAllocatorState::GlobalList }
            &&& !new_page.free_list_node_storage.is_init()
            &&& new_page.perm_2m.view().is_some()
            &&& new_page.perm_2m.view().unwrap().is_init()
            &&& new_page.perm_2m.view().unwrap().addr() == head_ptr
            &&& new_page.perm_2m.view().unwrap().value().view().len() == PAGE_SZ_2M
        } else {
            &&& new_page.state is Merged2m
            &&& new_page.free_list_node_storage.is_init()
            &&& new_page.perm_2m.view().is_none()
        }
    }
    &&& forall|i: usize| #![trigger post.pg_arr.spec_index(head).view().view().perm_2m.view().unwrap().value().view().subrange(i * PAGE_SZ_4K, (i + 1) * PAGE_SZ_4K)] i < 512 ==>
        post.pg_arr.spec_index(head).view().view().perm_2m.view().unwrap().value().view().subrange(i * PAGE_SZ_4K, (i + 1) * PAGE_SZ_4K)
            == pre.pg_arr.spec_index((head + i) as usize).view().view().perm_4k.view().unwrap().value().view()
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, thread)
    &&& post.thrd_mp.spec_index(thread).view() == (Thread { quota_4k: (pre.thrd_mp.spec_index(thread).view().quota_4k - 512) as usize,
        quota_2m: (pre.thrd_mp.spec_index(thread).view().quota_2m + 1) as usize, ..pre.thrd_mp.spec_index(thread).view() })
    &&& post.thrd_mp.spec_index(thread).is_init() == pre.thrd_mp.spec_index(thread).is_init()
    &&& post.thrd_mp.spec_index(thread).locking_thread() == pre.thrd_mp.spec_index(thread).locking_thread()
    &&& post.thrd_mp.spec_index(thread).being_killed() == pre.thrd_mp.spec_index(thread).being_killed()
    &&& post.thrd_mp.spec_index(thread).view_rodata() == pre.thrd_mp.spec_index(thread).view_rodata()
    &&& post.thrd_mp.spec_index(thread).view_ghost() == pre.thrd_mp.spec_index(thread).view_ghost()
    &&& post.thrd_mp.spec_index(thread).control() == pre.thrd_mp.spec_index(thread).control()
    &&& post.thrd_mp.spec_index(thread).killer_info() == pre.thrd_mp.spec_index(thread).killer_info()
    &&& forall|id: LockThreadId| #![trigger post.thrd_mp.spec_index(thread).locked_by_thread(id)] #![trigger pre.thrd_mp.spec_index(thread).locked_by_thread(id)]
        post.thrd_mp.spec_index(thread).locked_by_thread(id) == pre.thrd_mp.spec_index(thread).locked_by_thread(id)
    &&& forall|id: LockThreadId| #![trigger post.thrd_mp.spec_index(thread).rlocked_by_thread(id)] #![trigger pre.thrd_mp.spec_index(thread).rlocked_by_thread(id)]
        post.thrd_mp.spec_index(thread).rlocked_by_thread(id) == pre.thrd_mp.spec_index(thread).rlocked_by_thread(id)
    &&& forall|id: LockThreadId| #![trigger post.thrd_mp.spec_index(thread).wlocked_by_thread(id)] #![trigger pre.thrd_mp.spec_index(thread).wlocked_by_thread(id)]
        post.thrd_mp.spec_index(thread).wlocked_by_thread(id) == pre.thrd_mp.spec_index(thread).wlocked_by_thread(id)
    &&& forall|source: usize| #![trigger post.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source)] source <= NUM_CPUS ==>
        LinkedList::<PagePtr, 233>::values_sorted(post.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view())
    &&& forall|source: usize, pointer: PagePtr|
        #![trigger post.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(source).view().view().view().contains(pointer)]
        #![trigger pre.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(source).view().view().view().contains(pointer)]
        #![trigger post.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view().contains(pointer)]
        #![trigger pre.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view().contains(pointer)] source <= NUM_CPUS ==>
        post.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view().contains(pointer)
            == (pre.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view().contains(pointer) && !removed(source, pointer))
    &&& forall|source: usize, key: usize|
        #![trigger post.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(source).view().view().map().dom().contains(key)]
        #![trigger post.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).map().dom().contains(key)]
        #![trigger pre.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).map().dom().contains(key)] source <= NUM_CPUS ==> {
        let before = pre.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).map();
        let after = post.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).map();
        &&& after.dom().contains(key) == (before.dom().contains(key) && !removed(source, before.spec_index(key)))
        &&& after.dom().contains(key) ==> after.spec_index(key) == before.spec_index(key)
    }
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_4k)
    &&& post.allc_2m_mp.unchanged_except(&pre.allc_2m_mp, allocator_2m)
    &&& post.allc_4k_mp.spec_index(allocator_4k).total_free_pages.view() + 512 == pre.allc_4k_mp.spec_index(allocator_4k).total_free_pages.view()
    &&& post.allc_2m_mp.spec_index(allocator_2m).total_free_pages.view() == pre.allc_2m_mp.spec_index(allocator_2m).total_free_pages.view() + 1
    &&& post.allc_4k_mp.spec_index(allocator_4k).quota == pre.allc_4k_mp.spec_index(allocator_4k).quota
    &&& post.allc_2m_mp.spec_index(allocator_2m).quota == pre.allc_2m_mp.spec_index(allocator_2m).quota
    &&& post.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.allc_4k_mp.spec_index(allocator_4k).owning_container
    &&& post.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.allc_2m_mp.spec_index(allocator_2m).owning_container
    &&& post.allc_2m_mp.spec_index(allocator_2m).cpu_caches == pre.allc_2m_mp.spec_index(allocator_2m).cpu_caches
    &&& !pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().map().dom().contains(head_node)
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view().view() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().view().insert(0, head_ptr)
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view().map() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().map().insert(head_node, head_ptr)
    &&& forall|page: PagePtr| #![trigger post.allc_2m_mp.spec_index(allocator_2m).global_pool.view().view().contains(page)] #![trigger pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().view().contains(page)]
        post.allc_2m_mp.spec_index(allocator_2m).global_pool.view().view().contains(page) == (pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().view().contains(page) || page == head_ptr)
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.is_init() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.is_init()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view_rodata() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view_rodata()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view_ghost() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view_ghost()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.control() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.control()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.killer_info() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.killer_info()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view().line_pad == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().line_pad
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.minor == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.minor
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.container_depth == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.container_depth
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.is_init() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.is_init()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.control() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.control()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth
    &&& forall|cpu: CpuId| #![trigger post.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu)] cpu < NUM_CPUS ==> {
        let old_cache = pre.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view();
        let new_cache = post.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view();
        &&& new_cache.is_init() == old_cache.is_init()
        &&& new_cache.locking_thread() == old_cache.locking_thread()
        &&& new_cache.being_killed() == old_cache.being_killed()
        &&& new_cache.control() == old_cache.control()
        &&& new_cache.killer_info() == old_cache.killer_info()
        &&& new_cache.view_rodata() == old_cache.view_rodata()
        &&& new_cache.view_ghost() == old_cache.view_ghost()
        &&& new_cache.view().view().len() <= old_cache.view().view().len()
        &&& new_cache.view().line_pad == old_cache.view().line_pad
        &&& new_cache.view().linked_list.minor == old_cache.view().linked_list.minor
        &&& new_cache.view().linked_list.container_depth == old_cache.view().linked_list.container_depth

    }
}
}
