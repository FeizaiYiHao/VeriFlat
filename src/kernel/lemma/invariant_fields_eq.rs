use vstd::prelude::*;
use crate::*;

verus! {
/// Union of process fields read by invariants that frame a `quota_4k` update.
/// The changed `quota_4k` field and lock state are deliberately excluded.
pub open spec fn process_invariant_fields_except_quota_unchanged(pre: ProcessLockedMap, post: ProcessLockedMap) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger pre.spec_index(p_ptr)]
        #![trigger post.spec_index(p_ptr)]
        pre.dom().contains(p_ptr) ==> {
            &&& post.spec_index(p_ptr).view().zombie == pre.spec_index(p_ptr).view().zombie
            &&& post.spec_index(p_ptr).view_rodata() == pre.spec_index(p_ptr).view_rodata()
            &&& post.spec_index(p_ptr).view().pagetable == pre.spec_index(p_ptr).view().pagetable
            &&& post.spec_index(p_ptr).view().pcid == pre.spec_index(p_ptr).view().pcid
            &&& post.spec_index(p_ptr).view().iommu_table == pre.spec_index(p_ptr).view().iommu_table
            &&& post.spec_index(p_ptr).view_ghost().owned_pci_functions == pre.spec_index(p_ptr).view_ghost().owned_pci_functions
            &&& post.spec_index(p_ptr).view().parent_linkedlist_node == pre.spec_index(p_ptr).view().parent_linkedlist_node
            &&& post.spec_index(p_ptr).view().children == pre.spec_index(p_ptr).view().children
            &&& post.spec_index(p_ptr).view_ghost().uppertree_seq == pre.spec_index(p_ptr).view_ghost().uppertree_seq
            &&& post.spec_index(p_ptr).view_ghost().subtree_set == pre.spec_index(p_ptr).view_ghost().subtree_set
            &&& post.spec_index(p_ptr).view().owned_threads == pre.spec_index(p_ptr).view().owned_threads
        }
}

/// Union of allocator fields read by invariants that frame a quota-value
/// update. The changed quota value and all lock owners are excluded.
pub open spec fn allocator_invariant_fields_except_quota_unchanged(pre: PageAllocatorUnLockedMap, post: PageAllocatorUnLockedMap) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|a_ptr: RwLockPageAllocatorPtr|
        #![trigger pre.spec_index(a_ptr)]
        #![trigger post.spec_index(a_ptr)]
        pre.dom().contains(a_ptr) ==> {
            &&& post.spec_index(a_ptr).owning_container == pre.spec_index(a_ptr).owning_container
            &&& post.spec_index(a_ptr).quota.view().container_depth == pre.spec_index(a_ptr).quota.view().container_depth
            &&& post.spec_index(a_ptr).global_pool.view() == pre.spec_index(a_ptr).global_pool.view()
            &&& forall|cpu_id: CpuId|
                #![trigger pre.spec_index(a_ptr).cpu_caches.spec_index(cpu_id).view().view()]
                #![trigger post.spec_index(a_ptr).cpu_caches.spec_index(cpu_id).view().view()]
                index_valid(NUM_CPUS, cpu_id) ==> post.spec_index(a_ptr).cpu_caches.spec_index(cpu_id).view().view() == pre.spec_index(a_ptr).cpu_caches.spec_index(cpu_id).view().view()
        }
}

pub proof fn lemma_allocator_pages_wf_preserved_for_allocator_invariant_fields_except_quota_forall()
    ensures
        forall|page_array: PageLockedArray, pre: PageAllocatorUnLockedMap, post: PageAllocatorUnLockedMap, allocator_2m_map: PageAllocatorUnLockedMap, allocator_1g_map: PageAllocatorUnLockedMap|
            #![trigger allocator_pages_wf(page_array, pre, allocator_2m_map, allocator_1g_map), allocator_pages_wf(page_array, post, allocator_2m_map, allocator_1g_map)]
            allocator_pages_wf(page_array, pre, allocator_2m_map, allocator_1g_map) && allocator_invariant_fields_except_quota_unchanged(pre, post) ==> allocator_pages_wf(page_array, post, allocator_2m_map, allocator_1g_map),
{ reveal(allocator_4k_pages_wf); }

pub proof fn lemma_process_pages_wf_preserved_for_process_domain_eq_forall()
    ensures
        forall|page_array: PageLockedArray, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_pages_wf(page_array, pre), process_pages_wf(page_array, post)]
            process_pages_wf(page_array, pre) && post.dom() == pre.dom() ==> process_pages_wf(page_array, post),
{ reveal(process_pages_wf); }

pub proof fn lemma_container_process_page_pagetable_wf_preserved_for_process_invariant_fields_except_quota_forall()
    ensures
        forall|container_map: ContainerLockedMap, pre: ProcessLockedMap, post: ProcessLockedMap, pagetable_map: PageTableLockedMap, page_array: PageLockedArray|
            #![trigger container_process_page_pagetable_wf(container_map, pre, pagetable_map, page_array), container_process_page_pagetable_wf(container_map, post, pagetable_map, page_array)]
            container_process_page_pagetable_wf(container_map, pre, pagetable_map, page_array) && process_pagetable_match(pre, pagetable_map) && page_pagetable_wf(pagetable_map, page_array) && process_invariant_fields_except_quota_unchanged(pre, post)
                ==> container_process_page_pagetable_wf(container_map, post, pagetable_map, page_array),
{ reveal(container_process_page_pagetable_wf); }

pub proof fn lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall()
    ensures
        forall|pre: PageAllocatorUnLockedMap, post: PageAllocatorUnLockedMap|
            #![trigger allocator_free_page_ptrs_wf(pre), allocator_free_page_ptrs_wf(post)]
            allocator_free_page_ptrs_wf(pre) && post.dom() == pre.dom() && (forall|a_ptr: RwLockPageAllocatorPtr|
                #![trigger pre.spec_index(a_ptr)]
                #![trigger post.spec_index(a_ptr)]
                pre.dom().contains(a_ptr) ==> {
                    &&& post.spec_index(a_ptr).global_pool.view() == pre.spec_index(a_ptr).global_pool.view()
                    &&& forall|cpu_id: CpuId|
                        #![trigger pre.spec_index(a_ptr).cpu_caches.spec_index(cpu_id).view().view()]
                        #![trigger post.spec_index(a_ptr).cpu_caches.spec_index(cpu_id).view().view()]
                        index_valid(NUM_CPUS, cpu_id) ==> post.spec_index(a_ptr).cpu_caches.spec_index(cpu_id).view().view() == pre.spec_index(a_ptr).cpu_caches.spec_index(cpu_id).view().view()
                }) ==> allocator_free_page_ptrs_wf(post),
{ reveal(allocator_free_page_ptrs_wf); }

pub proof fn lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall()
    ensures
        forall|pre: ProcessLockedMap, post: ProcessLockedMap, pagetable_map: PageTableLockedMap|
            #![trigger process_pagetable_match(pre, pagetable_map), process_pagetable_match(post, pagetable_map)]
            process_pagetable_match(pre, pagetable_map) && post.dom() == pre.dom() && (forall|p_ptr: RwLockProcessPtr|
                #![trigger pre.spec_index(p_ptr)]
                #![trigger post.spec_index(p_ptr)]
                pre.dom().contains(p_ptr) ==> {
                    &&& post.spec_index(p_ptr).view().zombie == pre.spec_index(p_ptr).view().zombie
                    &&& post.spec_index(p_ptr).view_rodata() == pre.spec_index(p_ptr).view_rodata()
                    &&& post.spec_index(p_ptr).view().pagetable == pre.spec_index(p_ptr).view().pagetable
                    &&& post.spec_index(p_ptr).view().pcid == pre.spec_index(p_ptr).view().pcid
                }) ==> process_pagetable_match(post, pagetable_map),
{ reveal(process_pagetable_match); }

pub proof fn lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall()
    ensures
        forall|pre: ProcessLockedMap, post: ProcessLockedMap, iommu_table_map: IommuTableLockedMap|
            #![trigger process_iommu_table_match(pre, iommu_table_map), process_iommu_table_match(post, iommu_table_map)]
            process_iommu_table_match(pre, iommu_table_map) && post.dom() == pre.dom() && (forall|p_ptr: RwLockProcessPtr|
                #![trigger pre.spec_index(p_ptr)]
                #![trigger post.spec_index(p_ptr)]
                pre.dom().contains(p_ptr) ==> {
                    &&& post.spec_index(p_ptr).view().zombie == pre.spec_index(p_ptr).view().zombie
                    &&& post.spec_index(p_ptr).view_rodata() == pre.spec_index(p_ptr).view_rodata()
                    &&& post.spec_index(p_ptr).view().iommu_table == pre.spec_index(p_ptr).view().iommu_table
                }) ==> process_iommu_table_match(post, iommu_table_map),
{ reveal(process_iommu_table_match); }

pub proof fn lemma_iommu_root_table_process_wf_preserved_for_process_invariant_fields_except_quota_forall()
    ensures
        forall|root_table: IommuRootTable, pre: ProcessLockedMap, post: ProcessLockedMap, iommu_table_map: IommuTableLockedMap|
            #![trigger iommu_root_table_process_wf(root_table, pre, iommu_table_map), iommu_root_table_process_wf(root_table, post, iommu_table_map)]
            iommu_root_table_process_wf(root_table, pre, iommu_table_map) && process_invariant_fields_except_quota_unchanged(pre, post) ==> iommu_root_table_process_wf(root_table, post, iommu_table_map),
{ reveal(iommu_root_table_process_wf); }

pub proof fn lemma_process_pci_function_ownership_wf_preserved_for_process_invariant_fields_except_quota_forall()
    ensures
        forall|root_table: IommuRootTable, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger process_pci_function_ownership_wf(root_table, pre), process_pci_function_ownership_wf(root_table, post)]
            process_pci_function_ownership_wf(root_table, pre) && process_invariant_fields_except_quota_unchanged(pre, post) ==> process_pci_function_ownership_wf(root_table, post),
{ reveal(process_pci_function_ownership_wf); }

pub proof fn lemma_iommu_tlb_wf_spec_preserved_for_process_invariant_fields_except_quota_forall()
    ensures
        forall|iommu_tlb: IommuTLB, root_table: IommuRootTable, pre: ProcessLockedMap, post: ProcessLockedMap, iommu_table_map: IommuTableLockedMap|
            #![trigger iommu_tlb_wf_spec(iommu_tlb, root_table, pre, iommu_table_map), iommu_tlb_wf_spec(iommu_tlb, root_table, post, iommu_table_map)]
            iommu_tlb_wf_spec(iommu_tlb, root_table, pre, iommu_table_map) && iommu_root_table_process_wf(root_table, pre, iommu_table_map) && process_invariant_fields_except_quota_unchanged(pre, post)
                ==> iommu_tlb_wf_spec(iommu_tlb, root_table, post, iommu_table_map),
{ reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); }

pub proof fn lemma_container_process_wf_preserved_for_process_rodata_forall()
    ensures
        forall|container_map: ContainerLockedMap, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger container_process_wf(container_map, pre), container_process_wf(container_map, post)]
            container_process_wf(container_map, pre) && post.dom() == pre.dom() && (forall|p_ptr: RwLockProcessPtr|
                #![trigger pre.spec_index(p_ptr)]
                #![trigger post.spec_index(p_ptr)]
                pre.dom().contains(p_ptr) ==> {
                    &&& post.spec_index(p_ptr).view_rodata() == pre.spec_index(p_ptr).view_rodata()
                    &&& post.spec_index(p_ptr).view().zombie == pre.spec_index(p_ptr).view().zombie
                }) ==> container_process_wf(container_map, post),
{ reveal(container_process_wf); }

pub proof fn lemma_container_allocator_wf_preserved_for_allocator_invariant_fields_except_quota_forall()
    ensures
        forall|container_map: ContainerLockedMap, pre: PageAllocatorUnLockedMap, post: PageAllocatorUnLockedMap, allocator_2m_map: PageAllocatorUnLockedMap, allocator_1g_map: PageAllocatorUnLockedMap|
            #![trigger container_allocator_wf(container_map, pre, allocator_2m_map, allocator_1g_map), container_allocator_wf(container_map, post, allocator_2m_map, allocator_1g_map)]
            container_allocator_wf(container_map, pre, allocator_2m_map, allocator_1g_map) && allocator_invariant_fields_except_quota_unchanged(pre, post) ==> container_allocator_wf(container_map, post, allocator_2m_map, allocator_1g_map),
{ reveal(container_allocator_wf); }

pub proof fn container_allocator_wf_preserved_for_owner_depth_eq(
    old_container_map: ContainerLockedMap, new_container_map: ContainerLockedMap, old_allocator_4k_map: PageAllocatorUnLockedMap, new_allocator_4k_map: PageAllocatorUnLockedMap,
    old_allocator_2m_map: PageAllocatorUnLockedMap, new_allocator_2m_map: PageAllocatorUnLockedMap, old_allocator_1g_map: PageAllocatorUnLockedMap, new_allocator_1g_map: PageAllocatorUnLockedMap,
)
    requires
        container_allocator_wf(old_container_map, old_allocator_4k_map, old_allocator_2m_map, old_allocator_1g_map),
        new_container_map.dom() == old_container_map.dom(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_map.spec_index(c_ptr).view_rodata()]
            new_container_map.dom().contains(c_ptr) ==> new_container_map.spec_index(c_ptr).view_rodata() == old_container_map.spec_index(c_ptr).view_rodata(),
        new_allocator_4k_map.dom() == old_allocator_4k_map.dom(),
        forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger new_allocator_4k_map.spec_index(a_ptr)]
            new_allocator_4k_map.dom().contains(a_ptr) ==> {
                &&& new_allocator_4k_map.spec_index(a_ptr).owning_container == old_allocator_4k_map.spec_index(a_ptr).owning_container
                &&& new_allocator_4k_map.spec_index(a_ptr).quota.view().container_depth == old_allocator_4k_map.spec_index(a_ptr).quota.view().container_depth
            },
        new_allocator_2m_map.dom() == old_allocator_2m_map.dom(),
        forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger new_allocator_2m_map.spec_index(a_ptr)]
            new_allocator_2m_map.dom().contains(a_ptr) ==> {
                &&& new_allocator_2m_map.spec_index(a_ptr).owning_container == old_allocator_2m_map.spec_index(a_ptr).owning_container
                &&& new_allocator_2m_map.spec_index(a_ptr).quota.view().container_depth == old_allocator_2m_map.spec_index(a_ptr).quota.view().container_depth
            },
        new_allocator_1g_map.dom() == old_allocator_1g_map.dom(),
        forall|a_ptr: RwLockPageAllocatorPtr|
            #![trigger new_allocator_1g_map.spec_index(a_ptr)]
            new_allocator_1g_map.dom().contains(a_ptr) ==> {
                &&& new_allocator_1g_map.spec_index(a_ptr).owning_container == old_allocator_1g_map.spec_index(a_ptr).owning_container
                &&& new_allocator_1g_map.spec_index(a_ptr).quota.view().container_depth == old_allocator_1g_map.spec_index(a_ptr).quota.view().container_depth
            },
    ensures
        container_allocator_wf(new_container_map, new_allocator_4k_map, new_allocator_2m_map, new_allocator_1g_map),
{ reveal(container_allocator_wf); }

pub proof fn lemma_thread_staged_pages_wf_preserved_for_thread_invariant_fields_forall()
    ensures
        forall|pre: ThreadLockedMap, post: ThreadLockedMap, page_array: PageLockedArray|
            #![trigger thread_staged_pages_wf(pre, page_array), thread_staged_pages_wf(post, page_array)]
            thread_staged_pages_wf(pre, page_array) && thread_invariant_fields_unchanged(pre, post) ==> thread_staged_pages_wf(post, page_array),
{ reveal(thread_staged_pages_4k_wf); reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_1g_wf); }

pub proof fn lemma_per_container_process_tree_wf_preserved_for_process_invariant_fields_except_quota_forall()
    ensures
        forall|container_map: ContainerLockedMap, pre: ProcessLockedMap, post: ProcessLockedMap|
            #![trigger per_container_process_tree_wf(container_map, pre), per_container_process_tree_wf(container_map, post)]
            per_container_process_tree_wf(container_map, pre) && container_process_wf(container_map, pre) && process_invariant_fields_except_quota_unchanged(pre, post) ==> per_container_process_tree_wf(container_map, post),
{ reveal(per_container_process_tree_wf); reveal(container_process_wf); process_no_change_to_tree_fields_imply_wf_forall(); }

pub proof fn lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall()
    ensures
        forall|pre: ProcessLockedMap, post: ProcessLockedMap, cpu_array: CpuLockedArray|
            #![trigger process_cpu_wf(pre, cpu_array), process_cpu_wf(post, cpu_array)]
            process_cpu_wf(pre, cpu_array) && post.dom() == pre.dom() && (forall|p_ptr: RwLockProcessPtr|
                #![trigger pre.spec_index(p_ptr)]
                #![trigger post.spec_index(p_ptr)]
                pre.dom().contains(p_ptr) ==> {
                    &&& post.spec_index(p_ptr).view().zombie == pre.spec_index(p_ptr).view().zombie
                    &&& post.spec_index(p_ptr).view_rodata() == pre.spec_index(p_ptr).view_rodata()
                    &&& post.spec_index(p_ptr).view().pagetable == pre.spec_index(p_ptr).view().pagetable
                    &&& post.spec_index(p_ptr).view().pcid == pre.spec_index(p_ptr).view().pcid
                }) ==> process_cpu_wf(post, cpu_array),
{ reveal(process_cpu_wf); }

pub proof fn lemma_process_thread_wf_preserved_for_process_thread_membership_fields_forall()
    ensures
        forall|pre: ProcessLockedMap, post: ProcessLockedMap, thread_map: ThreadLockedMap|
            #![trigger process_thread_wf(pre, thread_map), process_thread_wf(post, thread_map)]
            process_thread_wf(pre, thread_map) && post.dom() == pre.dom() && (forall|p_ptr: RwLockProcessPtr|
                #![trigger pre.spec_index(p_ptr)]
                #![trigger post.spec_index(p_ptr)]
                pre.dom().contains(p_ptr) ==> {
                    &&& post.spec_index(p_ptr).view().zombie == pre.spec_index(p_ptr).view().zombie
                    &&& post.spec_index(p_ptr).view_rodata() == pre.spec_index(p_ptr).view_rodata()
                    &&& post.spec_index(p_ptr).view().owned_threads == pre.spec_index(p_ptr).view().owned_threads
                    &&& post.spec_index(p_ptr).view().pagetable == pre.spec_index(p_ptr).view().pagetable
                    &&& post.spec_index(p_ptr).being_killed() == pre.spec_index(p_ptr).being_killed()
                    &&& pre.spec_index(p_ptr).being_killed() ==> post.spec_index(p_ptr).locking_thread() == pre.spec_index(p_ptr).locking_thread()
                }) ==> process_thread_wf(post, thread_map),
{ reveal(process_thread_wf); }

pub proof fn lemma_cpu_dirty_map_wf_preserved_for_process_invariant_fields_except_quota_forall()
    ensures
        forall|container_map: ContainerLockedMap, cpu_set_map: CpuSetLockedMap, pre: ProcessLockedMap, post: ProcessLockedMap, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray, cpu_tlb: CpuTLB, pagetable_map: PageTableLockedMap|
            #![trigger cpu_dirty_map_wf(container_map, cpu_set_map, pre, cpu_array, cpu_tlb, pagetable_map, needflush), cpu_dirty_map_wf(container_map, cpu_set_map, post, cpu_array, cpu_tlb, pagetable_map, needflush)]
            cpu_dirty_map_wf(container_map, cpu_set_map, pre, cpu_array, cpu_tlb, pagetable_map, needflush) && process_cpu_wf(pre, cpu_array) && container_cpu_wf(container_map, cpu_set_map, cpu_array) && process_invariant_fields_except_quota_unchanged(pre, post)
                ==> cpu_dirty_map_wf(container_map, cpu_set_map, post, cpu_array, cpu_tlb, pagetable_map, needflush),
{ reveal(cpu_dirty_map_proc_pcid_match); }

pub proof fn process_pagetable_match_preserved_for_pagetable_fields_eq(process_map: ProcessLockedMap, old_pagetable_map: PageTableLockedMap, new_pagetable_map: PageTableLockedMap)
    requires
        process_pagetable_match(process_map, old_pagetable_map),
        new_pagetable_map.dom() == old_pagetable_map.dom(),
        forall|pt_ptr: RwLockPageTableRoot|
            #![trigger new_pagetable_map.spec_index(pt_ptr).view()]
            new_pagetable_map.dom().contains(pt_ptr) ==> {
                &&& new_pagetable_map.spec_index(pt_ptr).view().cr3 == old_pagetable_map.spec_index(pt_ptr).view().cr3
                &&& new_pagetable_map.spec_index(pt_ptr).view().proc_ptr == old_pagetable_map.spec_index(pt_ptr).view().proc_ptr
                &&& new_pagetable_map.spec_index(pt_ptr).view().pcid_value() == old_pagetable_map.spec_index(pt_ptr).view().pcid_value()
            },
    ensures
        process_pagetable_match(process_map, new_pagetable_map),
{ reveal(process_pagetable_match); }

pub proof fn process_pagetable_match_preserved_for_process_fields_eq(old_process_map: ProcessLockedMap, new_process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap)
    requires
        process_pagetable_match(old_process_map, pagetable_map),
        new_process_map.dom() == old_process_map.dom(),
        forall|proc_ptr: RwLockProcessPtr|
            #![trigger new_process_map.spec_index(proc_ptr).view()]
            new_process_map.dom().contains(proc_ptr) ==> {
                &&& new_process_map.spec_index(proc_ptr).view().pagetable == old_process_map.spec_index(proc_ptr).view().pagetable
                &&& new_process_map.spec_index(proc_ptr).view().pcid == old_process_map.spec_index(proc_ptr).view().pcid
                &&& new_process_map.spec_index(proc_ptr).view_rodata().view().pagetable == old_process_map.spec_index(proc_ptr).view_rodata().view().pagetable
                &&& new_process_map.spec_index(proc_ptr).view_rodata().view().pcid == old_process_map.spec_index(proc_ptr).view_rodata().view().pcid
                &&& new_process_map.spec_index(proc_ptr).view_rodata().view().cr3 == old_process_map.spec_index(proc_ptr).view_rodata().view().cr3
            },
    ensures
        process_pagetable_match(new_process_map, pagetable_map),
{ reveal(process_pagetable_match); }
}
