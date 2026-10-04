use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
/// Removes a page's final 4K mapping, returns the page to the allocator CPU
/// cache, and increments the owning thread's pending free-quota counter.
pub open spec fn reclaim_last_4k_mapping_to_cpu_cache_transition(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot,
    va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, depth: usize,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    old_counter: usize, new_counter: usize, node_addr: usize,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    let old_thread = pre.thr_mp.spec_index(thread_ptr);
    let new_thread = post.thr_mp.spec_index(thread_ptr);
    let old_allocator = pre.allc_4k_mp.spec_index(allocator_ptr);
    let new_allocator = post.allc_4k_mp.spec_index(allocator_ptr);
    &&& pre.pt_mp.dom().contains(pagetable)
    &&& va_4k_valid(va)
    &&& pre.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)
    &&& !pre.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present
    &&& pre.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).addr == page_ptr
    &&& page_ptr_valid(page_ptr)
    &&& old_page.view().ref_count == 1
    &&& old_page.view().state is Mapped4k
    &&& !old_page.view().is_io_page
    &&& old_page.view().owning_container == owner
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& pre.ctn_mp.dom().contains(owner)
    &&& pre.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
    &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
    &&& depth <= old_thread.view().container_depth
    &&& (if depth == old_thread.view().container_depth { owner == old_thread.view().owning_container } else { old_thread.view().upper_container_seq.view().spec_index(depth as int) == owner })
    &&& old_counter == old_thread.view().free_quota_pending_4k_at_depth(depth)
    &&& post == (KernelK { pt_mp: post.pt_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.pt_mp.dom() == pre.pt_mp.dom()
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& post.pt_mp.spec_index(pagetable).view().mapping_4k() == pre.pt_mp.spec_index(pagetable).view().mapping_4k().remove(va)
    &&& post.pt_mp.spec_index(pagetable).view().mapping_2m() == pre.pt_mp.spec_index(pagetable).view().mapping_2m()
    &&& post.pt_mp.spec_index(pagetable).view().mapping_1g() == pre.pt_mp.spec_index(pagetable).view().mapping_1g()
    &&& post.pt_mp.spec_index(pagetable).view().page_closure() == pre.pt_mp.spec_index(pagetable).view().page_closure()
    &&& post.pt_mp.spec_index(pagetable).view().kernel_entries == pre.pt_mp.spec_index(pagetable).view().kernel_entries
    &&& post.pt_mp.spec_index(pagetable).view().kernel_l4_end == pre.pt_mp.spec_index(pagetable).view().kernel_l4_end
    &&& post.pt_mp.spec_index(pagetable).view().cr3 == pre.pt_mp.spec_index(pagetable).view().cr3
    &&& post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr
    &&& post.pt_mp.spec_index(pagetable).view().pcid_value() == pre.pt_mp.spec_index(pagetable).view().pcid_value()
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& forall|i: PageIndex|
        #![trigger pre.pg_arr.spec_index(i).view().view().state]
        #![trigger post.pg_arr.spec_index(i).view().view().state]
        index_valid(NUM_PAGES, i) ==> {
            &&& post.pg_arr.spec_index(i).view().view().state == if i == page_index {
                PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            } else {
                pre.pg_arr.spec_index(i).view().view().state
            }
            &&& post.pg_arr.spec_index(i).view().view().owning_container == pre.pg_arr.spec_index(i).view().view().owning_container
            &&& (i != page_index ==> post.pg_arr.spec_index(i).view().view().mappings() == pre.pg_arr.spec_index(i).view().view().mappings())
        }
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view().free_list_node_storage.addr() == node_addr
    &&& old_page.view().free_list_node_storage.addr() == node_addr
    &&& new_page.view() == (Page {
        state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
        mappings: Ghost(old_page.view().mappings().remove((pagetable, va))),
        ref_count: 0,
        free_list_node_storage: new_page.view().free_list_node_storage,
        ..old_page.view()
    })
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr)
    &&& forall|t: RwLockThreadPtr|
        #![trigger pre.thr_mp.spec_index(t).view().temp_alloc_cache_4k]
        #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_4k]
        #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_2m]
        #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_1g]
        pre.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_4k == pre.thr_mp.spec_index(t).view().temp_alloc_cache_4k
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_2m == pre.thr_mp.spec_index(t).view().temp_alloc_cache_2m
            &&& post.thr_mp.spec_index(t).view().temp_alloc_cache_1g == pre.thr_mp.spec_index(t).view().temp_alloc_cache_1g
        }
    &&& new_thread.is_init() == old_thread.is_init()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& old_thread.locking_thread() is Write
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.view() == (Thread {
        direct_free_quota_pending_4k: new_thread.view().direct_free_quota_pending_4k,
        indirect_free_quota_pending_4k: new_thread.view().indirect_free_quota_pending_4k,
        ..old_thread.view()
    })
    &&& new_counter == old_counter + 1
    &&& new_thread.view().free_quota_pending_4k_at_depth(depth) == new_counter
    &&& new_thread.view().direct_free_quota_pending_4k.view() == old_thread.view().direct_free_quota_pending_4k.view() + if depth == old_thread.view().container_depth { 1int } else { 0int }
    &&& new_thread.view().indirect_free_quota_pending_4k.view() == if depth < old_thread.view().container_depth { old_thread.view().indirect_free_quota_pending_4k.view().update(depth as int, new_counter) } else { old_thread.view().indirect_free_quota_pending_4k.view() }
    &&& forall|t: RwLockThreadPtr|
        #![trigger pre.thr_mp.spec_index(t).view().direct_free_quota_pending_2m]
        #![trigger post.thr_mp.spec_index(t).view().direct_free_quota_pending_2m]
        #![trigger thread_effective_quota_1g(pre.thr_mp.spec_index(t))]
        #![trigger pre.thr_mp.spec_index(t).view().direct_free_quota_pending_1g]
        #![trigger pre.thr_mp.spec_index(t).view().indirect_free_quota_pending_1g]
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
    &&& new_allocator.quota == old_allocator.quota
    &&& new_allocator.total_free_pages.view() == old_allocator.total_free_pages.view() + 1
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().view() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().insert(0, page_ptr)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().map() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, page_ptr)
    &&& !old_allocator.cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr)
    &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread() == old_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread()
    &&& new_allocator.global_pool == old_allocator.global_pool
    &&& new_allocator.owning_container == old_allocator.owning_container
    &&& pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, pagetable, post.pt_mp.spec_index(pagetable).view())
}
}
