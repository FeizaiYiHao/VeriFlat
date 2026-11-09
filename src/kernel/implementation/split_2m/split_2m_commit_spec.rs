#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
pub open spec fn split_2m_exchange_thread_quotas_eof_transition_framing(pre: Thread, post: Thread) -> bool {
    post == (Thread { quota_4k: (pre.quota_4k + 512) as usize, quota_2m: (pre.quota_2m - 1) as usize, ..pre })
}

#[verifier::opaque]
pub open spec fn split_2m_commit_eof_transition_framing(pre: KernelK, post: KernelK,
    thread: RwLockThreadPtr, allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr,
    head: PageIndex, source: usize) -> bool {
    let region = Set::<PageIndex>::range(head, (head + 512) as usize);
    let head_node = pre.pg_arr.spec_index(head).view().view().free_list_node_storage.addr();
    &&& post == (KernelK { pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, ..pre })
    &&& forall|index: PageIndex| #![trigger post.pg_arr.spec_index(index)] #![trigger pre.pg_arr.spec_index(index)]
        index_valid(NUM_PAGES, index) && !region.contains(index) ==> post.pg_arr.spec_index(index) == pre.pg_arr.spec_index(index)
    &&& forall|index: PageIndex| #![trigger post.pg_arr.spec_index(index)]
        #![trigger pre.ctn_mp.spec_index(pre.pg_arr.spec_index(head).view().view().owning_container).view().owned_pages.view().contains(spec_page_index2page_ptr(index))] region.contains(index) ==> {
        let old_cell = pre.pg_arr.spec_index(index).view();
        let new_cell = post.pg_arr.spec_index(index).view();
        let old_page = old_cell.view();
        let new_page = new_cell.view();
        &&& (index != head ==> spec_page_index_merge_2m_valid(head, index))
        &&& new_cell.is_init() == old_cell.is_init()
        &&& new_cell.locking_thread() == old_cell.locking_thread()
        &&& new_cell.being_killed() == old_cell.being_killed()
        &&& new_cell.view_rodata() == old_cell.view_rodata()
        &&& new_cell.view_ghost() == old_cell.view_ghost()
        &&& new_cell.control() == old_cell.control()
        &&& new_cell.killer_info() == old_cell.killer_info()
        &&& post.pg_arr.lock_id_by_index(index) == pre.pg_arr.lock_id_by_index(index)
        &&& new_page == (Page { state: new_page.state, perm_4k: new_page.perm_4k, perm_2m: new_page.perm_2m,
            owning_container: pre.pg_arr.spec_index(head).view().view().owning_container,
            free_list_node_storage: new_page.free_list_node_storage, ..old_page })
        &&& new_page.state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state: FreePageAllocatorState::GlobalList }
        &&& new_page.perm_2m.view().is_none()
        &&& new_page.perm_4k.view().is_some()
        &&& new_page.perm_4k.view().unwrap().is_init()
        &&& new_page.perm_4k.view().unwrap().addr() == index * PAGE_SZ_4K
        &&& new_page.perm_4k.view().unwrap().value().view() == pre.pg_arr.spec_index(head).view().view().perm_2m.view().unwrap().value().view().subrange((index - head) * PAGE_SZ_4K, (index - head + 1) * PAGE_SZ_4K)
        &&& !new_page.free_list_node_storage.is_init()
        &&& new_page.free_list_node_storage.addr() == old_page.free_list_node_storage.addr()
    }
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, thread)
    &&& split_2m_exchange_thread_quotas_eof_transition_framing(pre.thrd_mp.spec_index(thread).view(), post.thrd_mp.spec_index(thread).view())
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
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_4k)
    &&& post.allc_4k_mp.spec_index(allocator_4k).quota == pre.allc_4k_mp.spec_index(allocator_4k).quota
    &&& post.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.allc_4k_mp.spec_index(allocator_4k).owning_container
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.is_init() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.is_init()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.being_killed() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.being_killed()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.control() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.control()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth
    &&& post.allc_2m_mp.unchanged_except(&pre.allc_2m_mp, allocator_2m)
    &&& post.allc_2m_mp.spec_index(allocator_2m).quota == pre.allc_2m_mp.spec_index(allocator_2m).quota
    &&& post.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.allc_2m_mp.spec_index(allocator_2m).owning_container
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.is_init() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.is_init()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.being_killed() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.being_killed()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view_rodata() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view_rodata()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view_ghost() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view_ghost()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.control() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.control()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.killer_info() == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.killer_info()
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view().line_pad == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().line_pad
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.minor == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.minor
    &&& post.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.container_depth == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.container_depth
    &&& pre.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(NUM_CPUS) == pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list
    &&& post.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(NUM_CPUS) == post.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list
    &&& post.allc_4k_mp.spec_index(allocator_4k).cpu_caches == pre.allc_4k_mp.spec_index(allocator_4k).cpu_caches
    &&& post.allc_4k_mp.spec_index(allocator_4k).total_free_pages.view() == pre.allc_4k_mp.spec_index(allocator_4k).total_free_pages.view() + 512
    &&& post.allc_2m_mp.spec_index(allocator_2m).total_free_pages.view() + 1 == pre.allc_2m_mp.spec_index(allocator_2m).total_free_pages.view()
    &&& post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().view() == Seq::new(512, |i: int| spec_page_index2page_ptr((head + 511 - i) as usize)) + pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().view()
    &&& forall|pointer: PagePtr| #![trigger post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().view().contains(pointer)] #![trigger pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().view().contains(pointer)]
        post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().view().contains(pointer)
            == (pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().view().contains(pointer)
                || (region.contains((pointer / 4096) as usize) && pointer == spec_page_index2page_ptr((pointer / 4096) as usize)))
    &&& forall|index: PageIndex| #![trigger post.pg_arr.spec_index(index)] region.contains(index) ==>
        post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().spec_index(post.pg_arr.spec_index(index).view().view().free_list_node_storage.addr()) == spec_page_index2page_ptr(index)
        && post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().dom().contains(post.pg_arr.spec_index(index).view().view().free_list_node_storage.addr())
    &&& forall|key: usize| #![trigger post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().spec_index(key)] #![trigger pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().dom().contains(key)]
        pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().dom().contains(key) ==>
        post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().dom().contains(key)
        && post.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().spec_index(key) == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().spec_index(key)
    &&& forall|s: usize| #![trigger post.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s)] #![trigger post.allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(s)] s <= NUM_CPUS ==> {
        let before = pre.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s);
        let after = post.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s);
        &&& (s != source ==> after == before)
        &&& after.view() == if s == source { before.view().skip(1) } else { before.view() }
        &&& after.map() == if s == source { before.map().remove(head_node) } else { before.map() }
        &&& forall|pointer: PagePtr| #![trigger after.view().contains(pointer)] #![trigger before.view().contains(pointer)]
            after.view().contains(pointer) == (before.view().contains(pointer) && !(s == source && pointer == spec_page_index2page_ptr(head)))
    }
    &&& forall|cpu: CpuId| #![trigger post.allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu)] cpu < NUM_CPUS ==> {
        let old_cache = pre.allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view();
        let new_cache = post.allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view();
        &&& new_cache.is_init() == old_cache.is_init()
        &&& new_cache.locking_thread() == old_cache.locking_thread()
        &&& new_cache.being_killed() == old_cache.being_killed()
        &&& new_cache.view_rodata() == old_cache.view_rodata()
        &&& new_cache.view_ghost() == old_cache.view_ghost()
        &&& new_cache.control() == old_cache.control()
        &&& new_cache.killer_info() == old_cache.killer_info()
        &&& new_cache.view().view().len() <= old_cache.view().view().len()
        &&& new_cache.view().line_pad == old_cache.view().line_pad
        &&& new_cache.view().linked_list.minor == old_cache.view().linked_list.minor
        &&& new_cache.view().linked_list.container_depth == old_cache.view().linked_list.container_depth
    }
}
}
