use vstd::prelude::*;
use crate::*;

verus! {
/// The table page `page_ptr` leaves the closure of the write-held page table `table` (the IOMMU table `table` when
/// `iommu`), every mapping staying, and returns through its free-list node at `node_addr` to shard `cpu_id` of the 4K
/// allocator `allocator_ptr` of its owner, the container of the write-held killer `thread_ptr`, whose direct pending
/// 4K refund grows by one.
#[verifier::opaque]
pub(crate) open spec fn kill_retire_table_page_eof_transition_framing(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    node_addr: usize,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    let old_thread = pre.thr_mp.spec_index(thread_ptr);
    let new_thread = post.thr_mp.spec_index(thread_ptr);
    let old_allocator = pre.allc_4k_mp.spec_index(allocator_ptr);
    let new_allocator = post.allc_4k_mp.spec_index(allocator_ptr);
    let free_state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } };
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, it_mp: post.it_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& if iommu {
        let old_table = pre.it_mp.spec_index(table);
        let new_table = post.it_mp.spec_index(table);
        &&& post.pt_mp == pre.pt_mp
        &&& post.pt_lower == pre.pt_lower
        &&& post.it_mp.dom() == pre.it_mp.dom()
        &&& post.it_mp.unchanged_except(&pre.it_mp, table)
        &&& new_table.locking_thread() == old_table.locking_thread()
        &&& new_table.being_killed() == old_table.being_killed()
        &&& new_table.view().page_closure() == old_table.view().page_closure().remove(page_ptr)
        &&& new_table.view().mapping_4k() == old_table.view().mapping_4k()
        &&& new_table.view().mapping_2m() == old_table.view().mapping_2m()
        &&& new_table.view().mapping_1g() == old_table.view().mapping_1g()
        &&& new_table.view().kernel_entries == old_table.view().kernel_entries
        &&& new_table.view().kernel_l4_end == old_table.view().kernel_l4_end
        &&& new_table.view().cr3 == old_table.view().cr3
        &&& new_table.view().pcid == old_table.view().pcid
        &&& new_table.view().proc_ptr == old_table.view().proc_ptr
        &&& new_table.view().did == old_table.view().did
    } else {
        let old_table = pre.pt_mp.spec_index(table);
        let new_table = post.pt_mp.spec_index(table);
        let old_c = pagetable_c(pre.pt_mp, pre.pt_lower.view(), table);
        let new_c = pagetable_c(post.pt_mp, post.pt_lower.view(), table);
        &&& post.it_mp == pre.it_mp
        &&& post.pt_mp.dom() == pre.pt_mp.dom()
        &&& post.pt_mp.unchanged_except(&pre.pt_mp, table)
        &&& post.pt_lower.view() == pre.pt_lower.view().insert(table, post.pt_lower.view().spec_index(table))
        &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), r)]
            pre.pt_mp.dom().contains(r) && r != table ==> pagetable_c(post.pt_mp, post.pt_lower.view(), r) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), r)
        &&& new_table.locking_thread() == old_table.locking_thread()
        &&& new_table.being_killed() == old_table.being_killed()
        &&& new_table.view_ghost() == post.pt_lower.view().spec_index(table)
        &&& new_c.page_closure() == old_c.page_closure().remove(page_ptr)
        &&& new_c.mapping_4k() == old_c.mapping_4k()
        &&& new_c.mapping_2m() == old_c.mapping_2m()
        &&& new_c.mapping_1g() == old_c.mapping_1g()
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger new_c.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
            old_table.view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.window_locked_by_thread(l4i, l3i, l2i, thread_id) == old_c.window_locked_by_thread(l4i, l3i, l2i, thread_id)
        &&& new_table.view().kernel_entries == old_table.view().kernel_entries
        &&& new_table.view().kernel_l4_end == old_table.view().kernel_l4_end
        &&& new_table.view().cr3 == old_table.view().cr3
        &&& new_table.view().pcid == old_table.view().pcid
        &&& new_table.view().proc_ptr == old_table.view().proc_ptr
    }
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& forall|i: PageIndex| #![trigger pre.pg_arr.spec_index(i).view().view().state] #![trigger post.pg_arr.spec_index(i).view().view().state]
        index_valid(NUM_PAGES, i) ==> {
            &&& post.pg_arr.spec_index(i).view().view().state == if i == page_index { free_state } else { pre.pg_arr.spec_index(i).view().view().state }
            &&& post.pg_arr.spec_index(i).view().view().owning_container == pre.pg_arr.spec_index(i).view().view().owning_container
            &&& post.pg_arr.spec_index(i).view().view().mappings() == pre.pg_arr.spec_index(i).view().view().mappings()
        }
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view().free_list_node_storage.addr() == node_addr
    &&& new_page.view() == (Page { state: free_state, free_list_node_storage: new_page.view().free_list_node_storage, perm_4k: new_page.view().perm_4k, ..old_page.view() })
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& forall|t: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(t).view().temp_alloc_cache_4k] #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_4k]
        #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_2m] #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_1g]
        pre.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_4k == pre.thr_mp.spec_index(t).view().temp_alloc_cache_4k
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_2m == pre.thr_mp.spec_index(t).view().temp_alloc_cache_2m
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_1g == pre.thr_mp.spec_index(t).view().temp_alloc_cache_1g
        }
    &&& new_thread.is_init() == old_thread.is_init()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view() == (Thread { direct_free_quota_pending_4k: new_thread.view().direct_free_quota_pending_4k, ..old_thread.view() })
    &&& new_thread.view().direct_free_quota_pending_4k.view() == old_thread.view().direct_free_quota_pending_4k.view() + 1
    &&& forall|t: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(t).view().direct_free_quota_pending_2m] #![trigger post.thr_mp.spec_index(t).view().direct_free_quota_pending_2m]
        #![trigger thread_effective_quota_1g(pre.thr_mp.spec_index(t))] #![trigger pre.thr_mp.spec_index(t).view().direct_free_quota_pending_1g] #![trigger pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g]
        pre.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).view().quota_2m == pre.thr_mp.spec_index(t).view().quota_2m
            &&& post.thr_mp.spec_index(t).view().quota_1g == pre.thr_mp.spec_index(t).view().quota_1g
            &&& post.thr_mp.spec_index(t).view().direct_free_quota_pending_2m == pre.thr_mp.spec_index(t).view().direct_free_quota_pending_2m
            &&& post.thr_mp.spec_index(t).view().direct_free_quota_pending_1g == pre.thr_mp.spec_index(t).view().direct_free_quota_pending_1g
            &&& post.thr_mp.spec_index(t).view().indirect_free_quota_pending_2m == pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_2m
            &&& post.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g == pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g
        }
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr)
    &&& new_allocator == (PageAllocator { cpu_caches: new_allocator.cpu_caches, total_free_pages: new_allocator.total_free_pages, ..old_allocator })
    &&& new_allocator.total_free_pages.view() == old_allocator.total_free_pages.view() + 1
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().view() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().insert(0, page_ptr)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().map() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, page_ptr)
    &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread() == old_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread()
}
} // verus!
