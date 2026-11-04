use vstd::prelude::*;
use crate::*;

verus! {
/// Removes a page's final 4K mapping, returns the page to the allocator CPU
/// cache, and increments the owning thread's pending free-quota counter.
#[verifier::opaque]
pub(super) open spec fn reclaim_last_4k_mapping_to_cpu_cache_eof_transition_framing(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, owner: RwLockContainerPtr,
    depth: usize, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, old_counter: usize, new_counter: usize, node_addr: usize,
) -> bool {
    let pg_idx = page_ptr2page_index(pg_ptr);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    let old_thread = pre.thrd_mp.spec_index(thrd_ptr);
    let new_thread = post.thrd_mp.spec_index(thrd_ptr);
    let old_allocator = pre.allc_4k_mp.spec_index(allc_ptr);
    let new_allocator = post.allc_4k_mp.spec_index(allc_ptr);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.pt_mp.dom() == pre.pt_mp.dom()
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().remove(va)
    &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m()
    &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g()
    &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).page_closure() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).page_closure()
    &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.window_stale_cpus == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.l2_entry(p, i)]
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.l2_entry(p, i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).spec_held_l2(l4i, l3i, l2i)]
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).spec_held_l2(l4i, l3i, l2i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != spec_va2index(va)
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)]
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)
    &&& post.pt_mp.spec_index(pagetable).view() == pre.pt_mp.spec_index(pagetable).view()
    &&& post.pt_mp.spec_index(pagetable).view().kernel_entries == pre.pt_mp.spec_index(pagetable).view().kernel_entries
    &&& post.pt_mp.spec_index(pagetable).view().kernel_l4_end == pre.pt_mp.spec_index(pagetable).view().kernel_l4_end
    &&& post.pt_mp.spec_index(pagetable).view().cr3 == pre.pt_mp.spec_index(pagetable).view().cr3
    &&& post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr
    &&& post.pt_mp.spec_index(pagetable).view().pcid_value() == pre.pt_mp.spec_index(pagetable).view().pcid_value()
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
        }
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view().free_list_node_storage.addr() == node_addr
    &&& new_page.view() == (Page {
        state: PageState::Free4k { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
        mappings: Ghost(old_page.view().mappings().remove((pagetable, va))), ref_count: 0, free_list_node_storage: new_page.view().free_list_node_storage, ..old_page.view()
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
