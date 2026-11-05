use vstd::prelude::*;
use crate::*;

verus! {
/// Removes a page's final mapping, a 4K leaf of a write-locked IOMMU table, returns the page to the allocator CPU cache,
/// and increments the owning thread's pending free-quota counter.
#[verifier::opaque]
pub(super) open spec fn reclaim_last_iommu_4k_mapping_to_cpu_cache_eof_transition_framing(
    pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, depth: usize,
    allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
) -> bool {
    let iova = spec_index2va(indices);
    let pg_idx = page_ptr2page_index(pg_ptr);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    let old_thread = pre.thrd_mp.spec_index(thrd_ptr);
    let new_thread = post.thrd_mp.spec_index(thrd_ptr);
    let old_allocator = pre.allc_4k_mp.spec_index(allc_ptr);
    let new_allocator = post.allc_4k_mp.spec_index(allc_ptr);
    &&& post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.it_mp.dom() == pre.it_mp.dom()
    &&& post.it_mp.unchanged_except(&pre.it_mp, iommu_table)
    &&& post.it_mp.spec_index(iommu_table).locking_thread() == pre.it_mp.spec_index(iommu_table).locking_thread()
    &&& post.it_mp.spec_index(iommu_table).being_killed() == pre.it_mp.spec_index(iommu_table).being_killed()
    &&& post.it_mp.spec_index(iommu_table).view().mapping_4k() == pre.it_mp.spec_index(iommu_table).view().mapping_4k().remove(iova)
    &&& post.it_mp.spec_index(iommu_table).view().mapping_2m() == pre.it_mp.spec_index(iommu_table).view().mapping_2m()
    &&& post.it_mp.spec_index(iommu_table).view().mapping_1g() == pre.it_mp.spec_index(iommu_table).view().mapping_1g()
    &&& post.it_mp.spec_index(iommu_table).view().page_closure() == pre.it_mp.spec_index(iommu_table).view().page_closure()
    &&& post.it_mp.spec_index(iommu_table).view().kernel_entries == pre.it_mp.spec_index(iommu_table).view().kernel_entries
    &&& post.it_mp.spec_index(iommu_table).view().kernel_l4_end == pre.it_mp.spec_index(iommu_table).view().kernel_l4_end
    &&& post.it_mp.spec_index(iommu_table).view().cr3 == pre.it_mp.spec_index(iommu_table).view().cr3
    &&& post.it_mp.spec_index(iommu_table).view().proc_ptr == pre.it_mp.spec_index(iommu_table).view().proc_ptr
    &&& post.it_mp.spec_index(iommu_table).view().pcid == pre.it_mp.spec_index(iommu_table).view().pcid
    &&& post.it_mp.spec_index(iommu_table).view().did == pre.it_mp.spec_index(iommu_table).view().did
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, pg_idx)
    &&& forall|i: PageIndex|
        #![trigger pre.pg_arr.spec_index(i).view().view().state]
        #![trigger post.pg_arr.spec_index(i).view().view().state]
        index_valid(NUM_PAGES, i) ==> {
            &&& post.pg_arr.spec_index(i).view().view().state == if i == pg_idx {
                PageState::Free4k { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            } else {
                pre.pg_arr.spec_index(i).view().view().state
            }
            &&& post.pg_arr.spec_index(i).view().view().owning_container == pre.pg_arr.spec_index(i).view().view().owning_container
            &&& (i != pg_idx ==> post.pg_arr.spec_index(i).view().view().mappings() == pre.pg_arr.spec_index(i).view().view().mappings())
            &&& (i != pg_idx ==> post.pg_arr.spec_index(i).view().view().iommu_mappings() == pre.pg_arr.spec_index(i).view().view().iommu_mappings())
        }
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view().free_list_node_storage.addr() == node_addr
    &&& new_page.view() == (Page {
        state: PageState::Free4k { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
        iommu_mappings: Ghost(old_page.view().iommu_mappings().remove((iommu_table, iova))), ref_count: 0, free_list_node_storage: new_page.view().free_list_node_storage, ..old_page.view()
    })
    &&& post.thrd_mp.dom() == pre.thrd_mp.dom()
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr)
    &&& forall|t: RwLockThreadPtr|
        #![trigger pre.thrd_mp.spec_index(t).view().temp_alloc_cache_4k]
        #![trigger post.thrd_mp.spec_index(t).view().temp_alloc_cache_4k]
        #![trigger post.thrd_mp.spec_index(t).view().temp_alloc_cache_2m]
        #![trigger post.thrd_mp.spec_index(t).view().temp_alloc_cache_1g]
        pre.thrd_mp.dom().contains(t) ==> {
            &&& post.thrd_mp.spec_index(t).view().temp_alloc_cache_4k == pre.thrd_mp.spec_index(t).view().temp_alloc_cache_4k
            &&& post.thrd_mp.spec_index(t).view().temp_alloc_cache_2m == pre.thrd_mp.spec_index(t).view().temp_alloc_cache_2m
            &&& post.thrd_mp.spec_index(t).view().temp_alloc_cache_1g == pre.thrd_mp.spec_index(t).view().temp_alloc_cache_1g
        }
    &&& new_thread.is_init() == old_thread.is_init()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view() == (Thread { direct_free_quota_pending_4k: new_thread.view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: new_thread.view().indirect_free_quota_pending_4k, ..old_thread.view() })
    &&& new_counter == old_counter + 1
    &&& new_thread.view().free_quota_pending_4k_at_depth(depth) == new_counter
    &&& new_thread.view().direct_free_quota_pending_4k.view() == old_thread.view().direct_free_quota_pending_4k.view() + if depth == old_thread.view().container_depth { 1int } else { 0int }
    &&& new_thread.view().indirect_free_quota_pending_4k.view() == if depth < old_thread.view().container_depth { old_thread.view().indirect_free_quota_pending_4k.view().update(depth as int, new_counter) } else { old_thread.view().indirect_free_quota_pending_4k.view() }
    &&& forall|t: RwLockThreadPtr|
        #![trigger pre.thrd_mp.spec_index(t).view().direct_free_quota_pending_2m]
        #![trigger post.thrd_mp.spec_index(t).view().direct_free_quota_pending_2m]
        #![trigger thread_effective_quota_1g(pre.thrd_mp.spec_index(t))]
        #![trigger pre.thrd_mp.spec_index(t).view().direct_free_quota_pending_1g]
        #![trigger pre.thrd_mp.spec_index(t).view().indirect_free_quota_pending_1g]
        pre.thrd_mp.dom().contains(t) ==> {
            &&& post.thrd_mp.spec_index(t).view().quota_2m == pre.thrd_mp.spec_index(t).view().quota_2m
            &&& post.thrd_mp.spec_index(t).view().quota_1g == pre.thrd_mp.spec_index(t).view().quota_1g
            &&& post.thrd_mp.spec_index(t).view().direct_free_quota_pending_2m == pre.thrd_mp.spec_index(t).view().direct_free_quota_pending_2m
            &&& post.thrd_mp.spec_index(t).view().direct_free_quota_pending_1g == pre.thrd_mp.spec_index(t).view().direct_free_quota_pending_1g
            &&& post.thrd_mp.spec_index(t).view().indirect_free_quota_pending_2m == pre.thrd_mp.spec_index(t).view().indirect_free_quota_pending_2m
            &&& post.thrd_mp.spec_index(t).view().indirect_free_quota_pending_1g == pre.thrd_mp.spec_index(t).view().indirect_free_quota_pending_1g
        }
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allc_ptr)
    &&& new_allocator.quota == old_allocator.quota
    &&& new_allocator.total_free_pages.view() == old_allocator.total_free_pages.view() + 1
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().view() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().insert(0, pg_ptr)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().map() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, pg_ptr)
    &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread() == old_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread()
    &&& new_allocator.global_pool == old_allocator.global_pool
    &&& new_allocator.owning_container == old_allocator.owning_container
}
}
