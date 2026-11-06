use vstd::prelude::*;
use crate::*;

verus! {
/// The final mapping of the 1G page `pg_ptr`, the held 1G leaf at `va` of the write-held page table `pagetable`, leaves the table with its record, and the page returns through its free-list node at `node_addr` to the global pool of its owner's 1G allocator `allc_ptr`, whose quota grows by
/// one; every other held entry of the table is unchanged.
#[verifier::opaque]
pub(crate) open spec fn kill_reclaim_held_1g_page_scoped_eof_transition_framing(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, node_addr: usize,
) -> bool {
    let pg_idx = page_ptr2page_index(pg_ptr);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    let old_allocator = pre.allc_1g_mp.spec_index(allc_ptr);
    let new_allocator = post.allc_1g_mp.spec_index(allc_ptr);
    &&& post == (KernelK { pt_mp: post.pt_mp, pg_arr: post.pg_arr, allc_1g_mp: post.allc_1g_mp, ..pre })
    &&& post.pt_lower == pre.pt_lower
    &&& post.pt_mp.dom() == pre.pt_mp.dom()
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& post.pt_mp.spec_index(pagetable).view_ghost() == pre.pt_mp.spec_index(pagetable).view_ghost()
    &&& new_c.lower == old_c.lower
    &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m()
    &&& new_c.higher == (PageTableHigher { l3_tables: new_c.higher.l3_tables, mapping_1g: new_c.higher.mapping_1g, ..old_c.higher })
    &&& new_c.mapping_1g() == old_c.mapping_1g().remove(va)
    &&& new_c.page_closure() == old_c.page_closure()
    &&& forall|l4i: L4Index| #![trigger new_c.spec_resolve_mapping_l4(l4i)] old_c.kernel_l4_end() <= l4i && pei_valid(l4i) ==> new_c.spec_resolve_mapping_l4(l4i) == old_c.spec_resolve_mapping_l4(l4i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_resolve_mapping_l3(l4i, l3i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> new_c.spec_resolve_mapping_l3(l4i, l3i) == old_c.spec_resolve_mapping_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_resolve_mapping_1g_l3(l4i, l3i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (spec_v2l4index(va), spec_v2l3index(va)) ==> new_c.spec_resolve_mapping_1g_l3(l4i, l3i) == old_c.spec_resolve_mapping_1g_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_resolve_mapping_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_resolve_mapping_l2(l4i, l3i, l2i) == old_c.spec_resolve_mapping_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == old_c.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index| #![trigger new_c.spec_held_l4(l4i)] old_c.kernel_l4_end() <= l4i && pei_valid(l4i) ==> new_c.spec_held_l4(l4i) == old_c.spec_held_l4(l4i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_l3(l4i, l3i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> new_c.spec_held_l3(l4i, l3i) == old_c.spec_held_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_1g_l3(l4i, l3i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (spec_v2l4index(va), spec_v2l3index(va)) ==> new_c.spec_held_1g_l3(l4i, l3i) == old_c.spec_held_1g_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& new_c.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
    &&& new_c.spec_resolve_mapping_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, pg_idx)
    &&& forall|i: PageIndex|
        #![trigger pre.pg_arr.spec_index(i).view().view().state]
        #![trigger post.pg_arr.spec_index(i).view().view().state]
        index_valid(NUM_PAGES, i) ==> {
            &&& post.pg_arr.spec_index(i).view().view().state == if i == pg_idx { PageState::Free1g { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::GlobalList } } else { pre.pg_arr.spec_index(i).view().view().state }
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
        state: PageState::Free1g { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::GlobalList },
        mappings: Ghost(old_page.view().mappings().remove((pagetable, va))), ref_count: 0, free_list_node_storage: new_page.view().free_list_node_storage, ..old_page.view()
    })
    &&& post.allc_1g_mp.dom() == pre.allc_1g_mp.dom()
    &&& post.allc_1g_mp.unchanged_except(&pre.allc_1g_mp, allc_ptr)
    &&& new_allocator.quota.view().value == old_allocator.quota.view().value + 1
    &&& new_allocator.quota.view() == (AllocatorQuota { value: new_allocator.quota.view().value, ..old_allocator.quota.view() })
    &&& new_allocator.quota.is_init() == old_allocator.quota.is_init()
    &&& new_allocator.quota.view_rodata() == old_allocator.quota.view_rodata()
    &&& new_allocator.quota.view_ghost() == old_allocator.quota.view_ghost()
    &&& new_allocator.quota.locking_thread() == old_allocator.quota.locking_thread()
    &&& new_allocator.quota.being_killed() == old_allocator.quota.being_killed()
    &&& new_allocator.total_free_pages.view() == old_allocator.total_free_pages.view() + 1
    &&& new_allocator.global_pool.view().view() == old_allocator.global_pool.view().view().insert(0, pg_ptr)
    &&& new_allocator.global_pool.view().map() == old_allocator.global_pool.view().map().insert(node_addr, pg_ptr)
    &&& new_allocator.global_pool.locking_thread() == old_allocator.global_pool.locking_thread()
    &&& new_allocator.cpu_caches == old_allocator.cpu_caches
    &&& new_allocator.owning_container == old_allocator.owning_container
}

/// The 4K and 2M mapping relations close after the last mapping of the 1G page `pg_ptr`, the held 1G leaf `va`, is dropped and cleared.
proof fn kill_reclaim_held_1g_page_scoped_eof_mapped_4k_2m_pages(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_held_1g_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr),
        pre.pt_mp.dom().contains(pagetable),
        page_ptr_valid(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped1g,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        post.subsystems_inv(),
    ensures
        mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
    reveal(kill_reclaim_held_1g_page_scoped_eof_transition_framing); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_lower_wf);
    assert(index_valid(NUM_PAGES, page_ptr2page_index(pg_ptr))) by { page_ptr_valid_imply_page_index_valid(); };
    pre.default_pagetable_wf_at(pagetable);
}

/// The 1G mapping relations close after the last mapping of the 1G page `pg_ptr`, the held 1G leaf `va`, is dropped and cleared.
proof fn kill_reclaim_held_1g_page_scoped_eof_mapped_1g_pages(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_held_1g_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr),
        ({
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_1g_valid(va)
            &&& old_c.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some
            &&& old_c.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == pg_ptr
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped1g
            &&& old_page.mappings().contains((pagetable, va))
        }),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        post.subsystems_inv(),
    ensures
        mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip, spec_index2va_2m_valid;
    reveal(kill_reclaim_held_1g_page_scoped_eof_transition_framing); reveal(mapped_1g_page_pagetable_wf); reveal(page_array_wf); reveal(pagetable_lower_wf);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    page_array_wf_at(pre.pg_arr, pg_idx);
    pre.default_pagetable_wf_at(pagetable);
    page_ptr_roundtrip(); page_index_roundtrip();
}

/// The page-table relations close after the last mapping of `pg_ptr`, the held 1G leaf `va`, is dropped and cleared.
proof fn kill_reclaim_held_1g_page_scoped_eof_page_relations(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_held_1g_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr),
        ({
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_1g_valid(va)
            &&& old_c.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some
            &&& old_c.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == pg_ptr
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped1g
            &&& old_page.mappings().contains((pagetable, va))
        }),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        post.subsystems_inv(),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
{
    reveal(kill_reclaim_held_1g_page_scoped_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    page_array_wf_at(pre.pg_arr, pg_idx);
    pre.default_pagetable_wf_at(pagetable);
    kill_reclaim_held_1g_page_scoped_eof_mapped_4k_2m_pages(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr);
    kill_reclaim_held_1g_page_scoped_eof_mapped_1g_pages(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr);
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(page_array_wf); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
}

/// The 1G allocator relations close after `pg_ptr` enters the head of the owner allocator's global pool.
proof fn kill_reclaim_held_1g_page_scoped_eof_free_1g_pages(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, node_addr: usize, owner: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_reclaim_held_1g_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.state is Mapped1g
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& pre.allc_1g_mp.dom().contains(allc_ptr)
            &&& !pre.allc_1g_mp.spec_index(allc_ptr).global_pool.view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_1g == allc_ptr
        }),
        post.subsystems_inv(),
    ensures
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        allocator_free_page_ptrs_wf(post.allc_1g_mp),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
        allocator_1g_cpu_caches_empty_wf(post.allc_1g_mp),
{
    reveal(kill_reclaim_held_1g_page_scoped_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_1g_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_1g_cpu_caches_empty_wf(post.allc_1g_mp)) by { reveal(allocator_1g_cpu_caches_empty_wf); };
    assert(allocator_cpu_cache_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(allocator_free_1g_pages_wf); reveal(allocator_cpu_cache_1g_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_global_pool_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by {
        reveal(allocator_free_1g_pages_wf); reveal(allocator_global_pool_1g_pages_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); reveal(page_array_wf);
        seq_insert_head_implies_contains::<PagePtr>(); page_ptr_roundtrip(); page_index_roundtrip();
    };
    reveal(allocator_free_1g_pages_wf);
}

/// The page ownership relations close after the 1G head `pg_ptr` turns from a mapped page into a free page of the owner allocator; its tails stay merged into it.
proof fn kill_reclaim_held_1g_page_scoped_eof_page_owners(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_held_1g_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr),
        page_ptr_valid(pg_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped1g,
        post.subsystems_inv(),
    ensures
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        container_owned_pages_wf(post.ctn_mp, post.pg_arr),
        container_pages_wf(post.ctn_mp, post.pg_arr),
        process_pages_wf(post.prc_mp, post.pg_arr),
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
        page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr),
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        thread_staged_pages_wf(post.thrd_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
{
    reveal(kill_reclaim_held_1g_page_scoped_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
    };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { container_pages_wf_preserved_for_page_state_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { process_pages_wf_preserved_for_page_state_eq(pre.prc_mp, post.prc_mp, pre.pg_arr, post.pg_arr); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { reveal(hugepage_1g_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by {
        thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, pg_idx); };
}

/// The 1G page that returns to its owner's 1G allocator carries one unit of quota, which that allocator's quota gains.
proof fn kill_reclaim_held_1g_page_scoped_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, node_addr: usize, owner: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_reclaim_held_1g_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.state is Mapped1g
            &&& old_page.mappings().contains((pagetable, va))
            &&& old_page.owning_container == owner
            &&& pre.allc_1g_mp.dom().contains(allc_ptr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_1g == allc_ptr
        }),
        post.subsystems_inv(),
    ensures
        container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(kill_reclaim_held_1g_page_scoped_eof_transition_framing);
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by { reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        let proc_ptr = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
        reveal(container_process_page_pagetable_wf); container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, proc_ptr); reveal(container_kill_retire_wf); reveal(container_allocator_wf);
    };
}

/// The CPU TLBs and paging-structure caches stay consistent after the held 1G leaf `va` of `pagetable` is cleared: it does not resolve and the table lists no CPU stale, so no TLB entry or cached directory entry names it.
proof fn kill_reclaim_held_1g_page_scoped_eof_cpu_caches(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, node_addr: usize,
)
    requires
        pre.inv(),
        kill_reclaim_held_1g_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr),
        pre.pt_mp.dom().contains(pagetable),
        va_1g_valid(va),
        pre.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None,
        pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(kill_reclaim_held_1g_page_scoped_eof_transition_framing);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); reveal(PageTableHigher::wf_mapping_1g);
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip;
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); };
}

/// Every invariant holds after the last mapping of the 1G page `pg_ptr`, a held leaf of `pagetable` that no longer resolves, is cleared and the page heads the global pool of its owner's 1G allocator `allc_ptr`, whose quota grows by one.
pub(crate) proof fn kill_reclaim_held_1g_page_scoped_eof(
    pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, allc_ptr: RwLockPageAllocatorPtr, node_addr: usize, owner: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_reclaim_held_1g_page_scoped_eof_transition_framing(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view();
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            &&& pre.pt_mp.dom().contains(pagetable)
            &&& va_1g_valid(va)
            &&& pre.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va)
            &&& old_c.spec_resolve_mapping_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
            &&& !old_c.mapping_1g().dom().contains(va)
            &&& pre.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& old_c.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some
            &&& old_c.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == pg_ptr
            &&& page_ptr_valid(pg_ptr)
            &&& old_page.ref_count == 1
            &&& old_page.state is Mapped1g
            &&& old_page.mappings().contains((pagetable, va))
            &&& old_page.owning_container == owner
            &&& old_page.free_list_node_storage.addr() == node_addr
            &&& pre.allc_1g_mp.dom().contains(allc_ptr)
            &&& !pre.allc_1g_mp.spec_index(allc_ptr).global_pool.view().map().dom().contains(node_addr)
            &&& pre.ctn_mp.dom().contains(owner)
            &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_1g == allc_ptr
        }),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().inv(),
        post.allc_1g_mp.perms_wf(),
        post.allc_1g_mp.spec_index(allc_ptr).wf(),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
{
    reveal(kill_reclaim_held_1g_page_scoped_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        reveal(page_array_wf); reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked);
    };
    kill_reclaim_held_1g_page_scoped_eof_page_relations(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr);
    kill_reclaim_held_1g_page_scoped_eof_free_1g_pages(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr, owner);
    kill_reclaim_held_1g_page_scoped_eof_page_owners(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr);
    kill_reclaim_held_1g_page_scoped_eof_allocator_quota_wf(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr, owner);
    assert(post.memory_management_inv()) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    kill_reclaim_held_1g_page_scoped_eof_cpu_caches(pre, post, pagetable, va, pg_ptr, allc_ptr, node_addr);
    assert(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() =~= whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g());
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
        kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
    };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp);
}
}
