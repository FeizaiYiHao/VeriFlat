use vstd::prelude::*;
use crate::*;

verus! {
/// The owner of the mapped page `p_i` that the leaf at `va` of the page table `pt_ptr` maps is the container of that
/// table's process or one of its ancestors.
pub proof fn container_process_page_pagetable_wf_page_at(
    container_map: ContainerLockedMap, process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, page_array: PageLockedArray, p_i: PageIndex, pt_ptr: RwLockPageTableRoot,
    va: VAddr,
)
    requires
        container_process_page_pagetable_wf(container_map, process_map, pagetable_map, page_array),
        index_valid(NUM_PAGES, p_i),
        page_array.spec_index(p_i).view().view().is_mapped(),
        page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va)),
    ensures
        ({
            let proc_ptr = pagetable_map.spec_index(pt_ptr).view().proc_ptr;
            let page_owner = page_array.spec_index(p_i).view().view().owning_container;
            &&& process_map.dom().contains(proc_ptr)
            &&& container_map.dom().contains(page_owner)
            &&& process_map.spec_index(proc_ptr).view_rodata().view().owning_container == page_owner
                || container_map.spec_index(page_owner).view_ghost().subtree_set.view().contains(process_map.spec_index(proc_ptr).view_rodata().view().owning_container)
        }),
{ reveal(container_process_page_pagetable_wf); }

/// The final mapping of the page `page_ptr`, the hidden 4K leaf at `va` of the write-held page table `pagetable`, leaves the
/// table, and the page returns through its free-list node at `node_addr` to shard `cpu_id` of the 4K allocator
/// `allocator_ptr` of its owner, whose quota grows by one.
#[verifier::opaque]
pub open spec fn kill_reclaim_unmapped_4k_page_scoped_eof_transition_framing(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    let old_allocator = pre.allc_4k_mp.spec_index(allocator_ptr);
    let new_allocator = post.allc_4k_mp.spec_index(allocator_ptr);
    let old_table = pre.pt_mp.spec_index(pagetable);
    let new_table = post.pt_mp.spec_index(pagetable);
    let old_c = pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.pt_mp.dom() == pre.pt_mp.dom()
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), r)]
        pre.pt_mp.dom().contains(r) && r != pagetable ==> pagetable_c(post.pt_mp, post.pt_lower.view(), r) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), r)
    &&& new_table.locking_thread() == old_table.locking_thread()
    &&& new_table.being_killed() == old_table.being_killed()
    &&& new_table.view_ghost() == post.pt_lower.view().spec_index(pagetable)
    &&& new_c.mapping_4k() == old_c.mapping_4k().remove(va)
    &&& new_c.mapping_2m() == old_c.mapping_2m()
    &&& new_c.mapping_1g() == old_c.mapping_1g()
    &&& new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.l2_lock == old_c.lower.l2_lock
    &&& new_table.view() == old_table.view()
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger new_c.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        old_table.view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.window_locked_by_thread(l4i, l3i, l2i, thread_id) == old_c.window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& new_table.view().kernel_entries == old_table.view().kernel_entries
    &&& new_table.view().kernel_l4_end == old_table.view().kernel_l4_end
    &&& new_table.view().cr3 == old_table.view().cr3
    &&& new_table.view().proc_ptr == old_table.view().proc_ptr
    &&& new_table.view().pcid_value() == old_table.view().pcid_value()
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& forall|i: PageIndex| #![trigger pre.pg_arr.spec_index(i).view().view().state] #![trigger post.pg_arr.spec_index(i).view().view().state]
        index_valid(NUM_PAGES, i) ==> {
            &&& post.pg_arr.spec_index(i).view().view().state == if i == page_index {
                PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            } else { pre.pg_arr.spec_index(i).view().view().state }
            &&& post.pg_arr.spec_index(i).view().view().owning_container == pre.pg_arr.spec_index(i).view().view().owning_container
            &&& (i != page_index ==> post.pg_arr.spec_index(i).view().view().mappings() == pre.pg_arr.spec_index(i).view().view().mappings())
        }
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view().free_list_node_storage.addr() == node_addr
    &&& new_page.view() == (Page {
        state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
        mappings: Ghost(old_page.view().mappings().remove((pagetable, va))), ref_count: 0, free_list_node_storage: new_page.view().free_list_node_storage, ..old_page.view()
    })
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr)
    &&& new_allocator.total_free_pages.view() == old_allocator.total_free_pages.view() + 1
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().view() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().insert(0, page_ptr)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().map() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, page_ptr)
    &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread() == old_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread()
    &&& new_allocator.global_pool == old_allocator.global_pool
    &&& new_allocator.owning_container == old_allocator.owning_container
    &&& new_allocator.quota.view().value == old_allocator.quota.view().value + 1
    &&& new_allocator.quota.view() == (AllocatorQuota { value: new_allocator.quota.view().value, ..old_allocator.quota.view() })
    &&& new_allocator.quota.is_init() == old_allocator.quota.is_init()
    &&& new_allocator.quota.view_rodata() == old_allocator.quota.view_rodata()
    &&& new_allocator.quota.view_ghost() == old_allocator.quota.view_ghost()
    &&& new_allocator.quota.locking_thread() == old_allocator.quota.locking_thread()
    &&& new_allocator.quota.being_killed() == old_allocator.quota.being_killed()
    &&& pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, pagetable, pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable))
}

/// The owner of the mapped page `p_i` that the leaf at `iova` of the IOMMU table `it_ptr` maps is the container of that
/// table's process or one of its ancestors.
pub proof fn page_iommu_table_wf_page_owner_at(
    container_map: ContainerLockedMap, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap, page_array: PageLockedArray, p_i: PageIndex, it_ptr: RwLockPageTableRoot,
    iova: VAddr,
)
    requires
        page_iommu_table_wf(container_map, process_map, iommu_table_map, page_array),
        index_valid(NUM_PAGES, p_i),
        page_array.spec_index(p_i).view().view().is_mapped(),
        page_array.spec_index(p_i).view().view().iommu_mappings().contains((it_ptr, iova)),
    ensures
        ({
            let proc_ptr = iommu_table_map.spec_index(it_ptr).view().proc_ptr;
            let page_owner = page_array.spec_index(p_i).view().view().owning_container;
            &&& process_map.dom().contains(proc_ptr)
            &&& container_map.dom().contains(page_owner)
            &&& process_map.spec_index(proc_ptr).view_rodata().view().owning_container == page_owner
                || container_map.spec_index(page_owner).view_ghost().subtree_set.view().contains(process_map.spec_index(proc_ptr).view_rodata().view().owning_container)
        }),
{ reveal(page_iommu_table_wf); }

/// The final mapping of the page `page_ptr`, the hidden 4K leaf at `indices` of the write-held IOMMU table `iommu_table`,
/// leaves the table, and the page returns through its free-list node at `node_addr` to shard `cpu_id` of the 4K allocator
/// `allocator_ptr` of its owner, whose quota grows by one.
#[verifier::opaque]
pub open spec fn kill_reclaim_unmapped_iommu_4k_page_scoped_eof_transition_framing(
    pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, allocator_ptr: RwLockPageAllocatorPtr,
    cpu_id: CpuId, node_addr: usize,
) -> bool {
    let iova = spec_index2va(indices);
    let page_index = page_ptr2page_index(page_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    let old_allocator = pre.allc_4k_mp.spec_index(allocator_ptr);
    let new_allocator = post.allc_4k_mp.spec_index(allocator_ptr);
    let old_table = pre.it_mp.spec_index(iommu_table);
    let new_table = post.it_mp.spec_index(iommu_table);
    &&& post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.it_mp.dom() == pre.it_mp.dom()
    &&& post.it_mp.unchanged_except(&pre.it_mp, iommu_table)
    &&& new_table.locking_thread() == old_table.locking_thread()
    &&& new_table.being_killed() == old_table.being_killed()
    &&& new_table.view().mapping_4k() == old_table.view().mapping_4k().remove(iova)
    &&& new_table.view().mapping_2m() == old_table.view().mapping_2m()
    &&& new_table.view().mapping_1g() == old_table.view().mapping_1g()
    &&& new_table.view().page_closure() == old_table.view().page_closure()
    &&& new_table.view().kernel_entries == old_table.view().kernel_entries
    &&& new_table.view().kernel_l4_end == old_table.view().kernel_l4_end
    &&& new_table.view().cr3 == old_table.view().cr3
    &&& new_table.view().proc_ptr == old_table.view().proc_ptr
    &&& new_table.view().pcid == old_table.view().pcid
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& forall|i: PageIndex| #![trigger pre.pg_arr.spec_index(i).view().view().state] #![trigger post.pg_arr.spec_index(i).view().view().state]
        index_valid(NUM_PAGES, i) ==> {
            &&& post.pg_arr.spec_index(i).view().view().state == if i == page_index {
                PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            } else { pre.pg_arr.spec_index(i).view().view().state }
            &&& post.pg_arr.spec_index(i).view().view().owning_container == pre.pg_arr.spec_index(i).view().view().owning_container
            &&& (i != page_index ==> post.pg_arr.spec_index(i).view().view().mappings() == pre.pg_arr.spec_index(i).view().view().mappings())
            &&& (i != page_index ==> post.pg_arr.spec_index(i).view().view().iommu_mappings() == pre.pg_arr.spec_index(i).view().view().iommu_mappings())
        }
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view().free_list_node_storage.addr() == node_addr
    &&& new_page.view() == (Page {
        state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
        iommu_mappings: Ghost(old_page.view().iommu_mappings().remove((iommu_table, iova))), ref_count: 0, free_list_node_storage: new_page.view().free_list_node_storage, ..old_page.view()
    })
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr)
    &&& new_allocator.total_free_pages.view() == old_allocator.total_free_pages.view() + 1
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().view() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().insert(0, page_ptr)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().map() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, page_ptr)
    &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread() == old_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread()
    &&& new_allocator.global_pool == old_allocator.global_pool
    &&& new_allocator.owning_container == old_allocator.owning_container
    &&& new_allocator.quota.view().value == old_allocator.quota.view().value + 1
    &&& new_allocator.quota.view() == (AllocatorQuota { value: new_allocator.quota.view().value, ..old_allocator.quota.view() })
    &&& new_allocator.quota.is_init() == old_allocator.quota.is_init()
    &&& new_allocator.quota.view_rodata() == old_allocator.quota.view_rodata()
    &&& new_allocator.quota.view_ghost() == old_allocator.quota.view_ghost()
    &&& new_allocator.quota.locking_thread() == old_allocator.quota.locking_thread()
    &&& new_allocator.quota.being_killed() == old_allocator.quota.being_killed()
}

/// The table page `page_ptr` leaves the closure of the write-held page table `table` (the IOMMU table `table` when
/// `iommu`), every mapping staying, and returns through its free-list node at `node_addr` to shard `cpu_id` of the 4K
/// allocator `allocator_ptr` of its owner, whose quota grows by one.
#[verifier::opaque]
pub open spec fn kill_retire_table_page_scoped_eof_transition_framing(
    pre: KernelK, post: KernelK, iommu: bool, table: RwLockPageTableRoot, page_ptr: PagePtr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, node_addr: usize,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    let old_allocator = pre.allc_4k_mp.spec_index(allocator_ptr);
    let new_allocator = post.allc_4k_mp.spec_index(allocator_ptr);
    let free_state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } };
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, it_mp: post.it_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..pre })
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
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr)
    &&& new_allocator == (PageAllocator { cpu_caches: new_allocator.cpu_caches, total_free_pages: new_allocator.total_free_pages, quota: new_allocator.quota, ..old_allocator })
    &&& new_allocator.total_free_pages.view() == old_allocator.total_free_pages.view() + 1
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().view() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().view().insert(0, page_ptr)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().view().map() == old_allocator.cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, page_ptr)
    &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
    &&& new_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread() == old_allocator.cpu_caches.spec_index(cpu_id).view().locking_thread()
    &&& new_allocator.quota.view().value == old_allocator.quota.view().value + 1
    &&& new_allocator.quota.view() == (AllocatorQuota { value: new_allocator.quota.view().value, ..old_allocator.quota.view() })
    &&& new_allocator.quota.is_init() == old_allocator.quota.is_init()
    &&& new_allocator.quota.view_rodata() == old_allocator.quota.view_rodata()
    &&& new_allocator.quota.view_ghost() == old_allocator.quota.view_ghost()
    &&& new_allocator.quota.locking_thread() == old_allocator.quota.locking_thread()
    &&& new_allocator.quota.being_killed() == old_allocator.quota.being_killed()
}
} // verus!
