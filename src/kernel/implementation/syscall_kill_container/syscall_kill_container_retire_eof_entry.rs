use vstd::prelude::*;
use crate::*;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_alloc_page::free_4k_page::kill_container_quota_fold::lemma_container_allocator_quota_eq_total_free_without_users;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::free_4k_page::kill_container_quota_fold::lemma_container_allocator_quota_eq_total_free_without_users;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_spec::*;

verus! {
/// The retired container `container_ptr` is marked and childless, has parent `parent_ptr` and `owner_ptr` in its upper
/// tree, owns no process, thread, indirect thread, or cpu, and has zero quotas.
pub open spec fn kill_container_retire_eof_target_empty(pre: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr) -> bool {
    let target = pre.ctn_mp.spec_index(container_ptr);
    let ro = target.view_rodata().view();
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& pre.ctn_mp.dom().contains(parent_ptr)
    &&& pre.ctn_mp.dom().contains(owner_ptr)
    &&& owner_ptr != container_ptr
    &&& target.being_killed()
    &&& target.view().children.view().len() == 0
    &&& target.view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty()
    &&& target.view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty()
    &&& target.view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty()
    &&& ro.parent == Some(parent_ptr)
    &&& target.view_ghost().uppertree_seq.view().contains(owner_ptr)
    &&& pre.cpu_set_mp.spec_index(ro.cpu_set).view().owned_cpus.view().is_empty()
    &&& pre.allc_4k_mp.spec_index(ro.allocator_ptr_4k).quota.view().value == 0
    &&& pre.allc_2m_mp.spec_index(ro.allocator_ptr_2m).quota.view().value == 0
    &&& pre.allc_1g_mp.spec_index(ro.allocator_ptr_1g).quota.view().value == 0
}

/// A childless container's subtree holds no container.
pub broadcast proof fn kill_container_retire_eof_subtree_empty(pre: KernelK, container_ptr: RwLockContainerPtr, sub: RwLockContainerPtr)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view().children.view().len() == 0,
    ensures !(#[trigger] pre.ctn_mp.spec_index(container_ptr).view_ghost().subtree_set.view().contains(sub)),
{
    if pre.ctn_mp.spec_index(container_ptr).view_ghost().subtree_set.view().contains(sub) {
        let d = pre.ctn_mp.spec_index(container_ptr).view_rodata().view().depth;
        let uppers = pre.ctn_mp.spec_index(sub).view_ghost().uppertree_seq.view();
        assert(pre.ctn_mp.dom().contains(sub) && uppers.len() > d && uppers[d as int] == container_ptr) by { reveal(container_subtree_set_wf); };
        container_perms_wf_at(pre.ctn_mp, container_ptr); container_perms_wf_at(pre.ctn_mp, sub);
        let x = if uppers.len() == d + 1 { sub } else { uppers[d + 1] };
        if uppers.len() != d + 1 {
            assert(uppers.contains(x));
            container_uppertree_seq_wf_at(pre.rt_ctn, pre.ctn_mp, sub, x); container_perms_wf_at(pre.ctn_mp, x);
        }
        assert(pre.ctn_mp.dom().contains(x));
        assert(pre.ctn_mp.spec_index(x).view_rodata().view().depth == d + 1);
        assert(pre.ctn_mp.spec_index(x).view_ghost().uppertree_seq.view()[d as int] == container_ptr);
        container_root_wf_at(pre.rt_ctn, pre.ctn_mp, x);
        assert(pre.ctn_mp.spec_index(x).view_rodata().view().parent == Some(container_ptr)) by { reveal(container_children_depth_wf); };
        assert(pre.ctn_mp.spec_index(container_ptr).view().children.view().contains(x)) by { reveal(container_children_parent_wf); };
    }
}

/// An endpoint whose owner is a childless container without threads has no holder `m`: every holder of an endpoint
/// lives in its owner's subtree.
pub broadcast proof fn kill_container_retire_eof_no_endpoint_holder(pre: KernelK, e: RwLockEndpointPtr, m: (RwLockThreadPtr, EndpointIdx))
    requires
        pre.inv(),
        pre.ep_mp.dom().contains(e),
        pre.ctn_mp.dom().contains(pre.ep_mp.spec_index(e).view().owning_container),
        pre.ctn_mp.spec_index(pre.ep_mp.spec_index(e).view().owning_container).view().children.view().len() == 0,
        pre.ctn_mp.spec_index(pre.ep_mp.spec_index(e).view().owning_container).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
    ensures !(#[trigger] pre.ep_mp.spec_index(e).view().owning_threads.view().contains(m)),
{
    let (t, idx) = m;
    assert(m == (t, idx));
    assert(!pre.ep_mp.spec_index(e).view().owning_threads.view().contains((t, idx))) by {
        reveal(thread_endpoint_ref_counter_wf); reveal(container_thread_endpoint_wf); reveal(container_thread_wf); broadcast use kill_container_retire_eof_subtree_empty;
    };
}

/// A childless container without threads owns no endpoint: every endpoint has a holder in its owner's subtree.
pub broadcast proof fn kill_container_retire_eof_no_endpoint(pre: KernelK, container_ptr: RwLockContainerPtr, e: RwLockEndpointPtr)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view().children.view().len() == 0,
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
    ensures !(#[trigger] pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_endpoints.view().contains(e)),
{
    if pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_endpoints.view().contains(e) {
        assert(pre.ep_mp.dom().contains(e) && pre.ep_mp.spec_index(e).view().owning_container == container_ptr) by { reveal(container_endpoint_wf); };
        let endpoint = pre.ep_mp.spec_index(e).view();
        reveal(endpoint_perms_wf);
        assert(endpoint.rf_counter == endpoint.owning_threads.view().len() && endpoint.rf_counter != 0);
        assert(endpoint.owning_threads.view() =~= Set::<(RwLockThreadPtr, EndpointIdx)>::empty()) by { broadcast use kill_container_retire_eof_no_endpoint_holder; };
    }
}

/// A mapped page whose owner is a childless container without processes records no page-table or IOMMU mapping `m`:
/// every mapping belongs to a process in its owner's subtree.
pub broadcast proof fn kill_container_retire_eof_no_mapping(pre: KernelK, i: PageIndex, m: (RwLockPageTableRoot, VAddr))
    requires
        pre.inv(),
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().is_mapped(),
        pre.ctn_mp.spec_index(pre.pg_arr.spec_index(i).view().view().owning_container).view().children.view().len() == 0,
        pre.ctn_mp.spec_index(pre.pg_arr.spec_index(i).view().view().owning_container).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
    ensures
        #![trigger pre.pg_arr.spec_index(i).view().view().mappings().contains(m)]
        #![trigger pre.pg_arr.spec_index(i).view().view().iommu_mappings().contains(m)]
        !pre.pg_arr.spec_index(i).view().view().mappings().contains(m) && !pre.pg_arr.spec_index(i).view().view().iommu_mappings().contains(m),
{
    let (table, va) = m;
    assert(m == (table, va));
    container_page_owner_backward_at(pre.ctn_mp, pre.pg_arr, i);
    assert(!pre.pg_arr.spec_index(i).view().view().mappings().contains((table, va))) by {
        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); broadcast use kill_container_retire_eof_subtree_empty;
    };
    assert(!pre.pg_arr.spec_index(i).view().view().iommu_mappings().contains((table, va))) by {
        reveal(page_iommu_table_wf); reveal(container_process_wf); broadcast use kill_container_retire_eof_subtree_empty;
    };
}

/// A page owned by a childless container without processes is not mapped.
proof fn kill_container_retire_eof_no_mapped_page_at(pre: KernelK, container_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view().children.view().len() == 0,
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == container_ptr,
    ensures !pre.pg_arr.spec_index(i).view().view().is_mapped(),
{
    let page = pre.pg_arr.spec_index(i).view().view();
    if page.is_mapped() {
        page_array_wf_at(pre.pg_arr, i);
        assert(page.mappings() =~= Set::<(RwLockPageTableRoot, VAddr)>::empty() && page.iommu_mappings() =~= Set::<(RwLockPageTableRoot, VAddr)>::empty()) by {
            broadcast use kill_container_retire_eof_no_mapping;
        };
    }
}

/// A page owned by a container without processes is no process object page and no page of a process's tables.
proof fn kill_container_retire_eof_no_process_page_at(pre: KernelK, container_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == container_ptr,
    ensures !page_state_is_process_kernel_page(pre.pg_arr.spec_index(i).view().view().state),
{
    let state = pre.pg_arr.spec_index(i).view().view().state;
    if page_state_is_process_kernel_page(state) {
        process_kernel_pages_owner_wf_at(pre.pg_arr, pre.prc_mp, pre.pt_mp, pre.it_mp, i);
        reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match);
        if state->Allocated4k_state is AsPageTableRoot {
            assert(state->Allocated4k_state->AsPageTableRoot_table_type == PT_TYPE || state->Allocated4k_state->AsPageTableRoot_table_type == IOMMU_TYPE);
        } else if state->Allocated4k_state is PageTable {
            assert(state->Allocated4k_state->PageTable_table_type == PT_TYPE || state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE);
        }
    }
}

/// A page owned by a container without processes, threads, or indirect threads and with zero 4K quota is not a free
/// 4K page: its 4K allocator holds no free page.
proof fn kill_container_retire_eof_no_free_4k_page_at(pre: KernelK, container_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value == 0,
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == container_ptr,
    ensures !(pre.pg_arr.spec_index(i).view().view().state is Free4k),
{
    let page = pre.pg_arr.spec_index(i).view().view();
    if page.state is Free4k {
        lemma_container_allocator_quota_eq_total_free_without_users(pre, container_ptr);
        container_allocator_free_4k_page_wf_at(pre.allc_4k_mp, pre.pg_arr, i);
        let a = page.state->Free4k_allocator_ptr.view();
        assert(pre.allc_4k_mp.dom().contains(a) && pre.allc_4k_mp.spec_index(a).owning_container == container_ptr);
        assert(a == pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k) by { reveal(container_allocator_wf); };
        let allocator = pre.allc_4k_mp.spec_index(a);
        allocator_perms_wf_at(pre.allc_4k_mp, a);
        if page.state->Free4k_state is PreCpuCache {
            let cpu = page.state->Free4k_state->PreCpuCache_cpu_id;
            allocator.cpu_caches.lemma_view_index(); lemma_cache_len_fold_ge_elem(allocator.cpu_caches.view(), cpu as int);
            allocator.cpu_caches.spec_index(cpu).view().view().linked_list.lemma_len_view();
        } else {
            lemma_cache_len_fold_nonneg(allocator.cpu_caches.view()); allocator.global_pool.view().lemma_len_view();
        }
    }
}

/// A page owned by a container without processes, threads, or indirect threads and with zero 2M quota is not a free
/// 2M page: its 2M allocator holds no free page.
proof fn kill_container_retire_eof_no_free_2m_page_at(pre: KernelK, container_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m).quota.view().value == 0,
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == container_ptr,
    ensures !(pre.pg_arr.spec_index(i).view().view().state is Free2m),
{
    let page = pre.pg_arr.spec_index(i).view().view();
    if page.state is Free2m {
        lemma_container_allocator_quota_eq_total_free_without_users(pre, container_ptr);
        container_allocator_free_2m_page_wf_at(pre.allc_2m_mp, pre.pg_arr, i);
        let a = page.state->Free2m_allocator_ptr.view();
        assert(pre.allc_2m_mp.dom().contains(a) && pre.allc_2m_mp.spec_index(a).owning_container == container_ptr);
        assert(a == pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m) by { reveal(container_allocator_wf); };
        let allocator = pre.allc_2m_mp.spec_index(a);
        allocator_perms_wf_at(pre.allc_2m_mp, a);
        if page.state->Free2m_state is PreCpuCache {
            let cpu = page.state->Free2m_state->PreCpuCache_cpu_id;
            allocator.cpu_caches.lemma_view_index(); lemma_cache_len_fold_ge_elem(allocator.cpu_caches.view(), cpu as int);
            allocator.cpu_caches.spec_index(cpu).view().view().linked_list.lemma_len_view();
        } else {
            lemma_cache_len_fold_nonneg(allocator.cpu_caches.view()); allocator.global_pool.view().lemma_len_view();
        }
    }
}

/// A page owned by a container without processes, threads, or indirect threads and with zero 1G quota is not a free
/// 1G page: its 1G allocator holds no free page.
proof fn kill_container_retire_eof_no_free_1g_page_at(pre: KernelK, container_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g).quota.view().value == 0,
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == container_ptr,
    ensures !(pre.pg_arr.spec_index(i).view().view().state is Free1g),
{
    let page = pre.pg_arr.spec_index(i).view().view();
    if page.state is Free1g {
        lemma_container_allocator_quota_eq_total_free_without_users(pre, container_ptr);
        let a = page.state->Free1g_allocator_ptr.view();
        let ptr = page_index2page_ptr(i);
        if page.state->Free1g_state is PreCpuCache {
            let cpu = page.state->Free1g_state->PreCpuCache_cpu_id;
            assert(index_valid(NUM_CPUS, cpu) && pre.allc_1g_mp.dom().contains(a) && pre.allc_1g_mp.spec_index(a).owning_container == container_ptr
                && pre.allc_1g_mp.spec_index(a).cpu_caches.spec_index(cpu).view().view().view().contains(ptr)) by {
                reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf);
            };
        } else {
            assert(pre.allc_1g_mp.dom().contains(a) && pre.allc_1g_mp.spec_index(a).owning_container == container_ptr && pre.allc_1g_mp.spec_index(a).global_pool.view().view().contains(ptr)) by {
                reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf);
            };
        }
        assert(a == pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g) by { reveal(container_allocator_wf); };
        let allocator = pre.allc_1g_mp.spec_index(a);
        allocator_perms_wf_at(pre.allc_1g_mp, a);
        if page.state->Free1g_state is PreCpuCache {
            let cpu = page.state->Free1g_state->PreCpuCache_cpu_id;
            allocator.cpu_caches.lemma_view_index(); lemma_cache_len_fold_ge_elem(allocator.cpu_caches.view(), cpu as int);
            allocator.cpu_caches.spec_index(cpu).view().view().linked_list.lemma_len_view();
        } else {
            lemma_cache_len_fold_nonneg(allocator.cpu_caches.view()); allocator.global_pool.view().lemma_len_view();
        }
    }
}

/// A page owned by a container without processes, threads, indirect threads, or quota is not free.
proof fn kill_container_retire_eof_no_free_page_at(pre: KernelK, container_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value == 0,
        pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m).quota.view().value == 0,
        pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g).quota.view().value == 0,
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == container_ptr,
    ensures !pre.pg_arr.spec_index(i).view().view().is_free(),
{
    kill_container_retire_eof_no_free_4k_page_at(pre, container_ptr, i); kill_container_retire_eof_no_free_2m_page_at(pre, container_ptr, i);
    kill_container_retire_eof_no_free_1g_page_at(pre, container_ptr, i);
}

/// A 2M head page owned by the retired container is one of its two 2M object pages.
proof fn kill_container_retire_eof_owned_head_2m_at(pre: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr),
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == container_ptr,
        page_state_2m_related(pre.pg_arr.spec_index(i).view().view().state),
        !(pre.pg_arr.spec_index(i).view().view().state is Merged2m),
    ensures
        i == page_ptr2page_index(container_ptr) || i == page_ptr2page_index(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator),
{
    let state = pre.pg_arr.spec_index(i).view().view().state;
    kill_container_retire_eof_no_free_page_at(pre, container_ptr, i); kill_container_retire_eof_no_mapped_page_at(pre, container_ptr, i);
    page_object_owner_wf_at(pre.pg_arr, pre.ctn_mp, pre.thr_mp, i); page_index_roundtrip();
    if state is Owned2m { container_thread_wf_at(pre.ctn_mp, pre.thr_mp, state->Owned2m_thread_ptr); }
    assert(state is Allocated2m);
    assert(state->Allocated2m_state is AsContainer || state->Allocated2m_state is AsPcidAllocator);
}

/// A page the retired container `container_ptr` owns is one of its five 4K object pages, one of its two 2M object
/// pages, or a tail of one of those.
proof fn kill_container_retire_eof_owned_page_at(pre: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr),
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == container_ptr,
    ensures
        ({
            let ro = pre.ctn_mp.spec_index(container_ptr).view_rodata().view();
            ||| i == page_ptr2page_index(ro.scheduler) || i == page_ptr2page_index(ro.cpu_set) || i == page_ptr2page_index(ro.allocator_ptr_4k)
            ||| i == page_ptr2page_index(ro.allocator_ptr_2m) || i == page_ptr2page_index(ro.allocator_ptr_1g)
            ||| i == page_ptr2page_index(container_ptr) || i == page_ptr2page_index(ro.pcid_allocator)
            ||| page_2m_tail_indices(page_ptr2page_index(container_ptr)).contains(i) || page_2m_tail_indices(page_ptr2page_index(ro.pcid_allocator)).contains(i)
        }),
{
    let ro = pre.ctn_mp.spec_index(container_ptr).view_rodata().view();
    let state = pre.pg_arr.spec_index(i).view().view().state;
    page_index_roundtrip();
    page_object_owner_wf_at(pre.pg_arr, pre.ctn_mp, pre.thr_mp, i);
    kill_container_retire_eof_no_free_page_at(pre, container_ptr, i); kill_container_retire_eof_no_mapped_page_at(pre, container_ptr, i);
    kill_container_retire_eof_no_process_page_at(pre, container_ptr, i);
    if state is Owned4k || state is Owned2m || state is Owned1g {
        let t = if state is Owned4k { state->Owned4k_thread_ptr } else if state is Owned2m { state->Owned2m_thread_ptr } else { state->Owned1g_thread_ptr };
        container_thread_wf_at(pre.ctn_mp, pre.thr_mp, t);
    }
    if state is Merged2m {
        let h = spec_page_index_truncate_2m(i);
        assert(h <= i < h + 512 && h % 512 == 0) by (nonlinear_arith) requires h == (i / 512usize * 512usize) as usize, i < NUM_PAGES {};
        assert(page_state_2m_related(pre.pg_arr.spec_index(h).view().view().state) && !(pre.pg_arr.spec_index(h).view().view().state is Merged2m)) by { reveal(hugepage_2m_wf); };
        hugepage_2m_wf_tail_at(pre.pg_arr, h, i);
        kill_container_retire_eof_owned_head_2m_at(pre, container_ptr, parent_ptr, owner_ptr, h);
    } else if state is Merged1g {
        let h = spec_page_index_truncate_1g(i);
        assert(h <= i < h + 0x40000) by (nonlinear_arith) requires h == (i / 512usize / 512usize * 512usize * 512usize) as usize, i < NUM_PAGES {};
        assert(pre.pg_arr.spec_index(h).view().view().state is Free1g || pre.pg_arr.spec_index(h).view().view().state is Mapped1g) by { reveal(hugepage_1g_wf); };
        assert(pre.pg_arr.spec_index(i).view().view().owning_container == pre.pg_arr.spec_index(h).view().view().owning_container) by { reveal(hugepage_1g_wf); };
        kill_container_retire_eof_no_free_page_at(pre, container_ptr, h); kill_container_retire_eof_no_mapped_page_at(pre, container_ptr, h);
    } else if state is Allocated2m {
        kill_container_retire_eof_owned_head_2m_at(pre, container_ptr, parent_ptr, owner_ptr, i);
    } else if state is Allocated4k {
        assert(state->Allocated4k_state is AsEndpoint ==> pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_endpoints.view().contains(page_index2page_ptr(i)));
        kill_container_retire_eof_no_endpoint(pre, container_ptr, page_index2page_ptr(i));
    }
}

/// Every page the retired container `container_ptr` owns is one of its object pages or their tails.
pub broadcast proof fn kill_container_retire_eof_owned_page(pre: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr),
    ensures
        #![trigger kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr), pre.pg_arr.spec_index(i).view().view().owning_container]
        index_valid(NUM_PAGES, i) && pre.pg_arr.spec_index(i).view().view().owning_container == container_ptr ==> ({
            let ro = pre.ctn_mp.spec_index(container_ptr).view_rodata().view();
            ||| i == page_ptr2page_index(ro.scheduler) || i == page_ptr2page_index(ro.cpu_set) || i == page_ptr2page_index(ro.allocator_ptr_4k)
            ||| i == page_ptr2page_index(ro.allocator_ptr_2m) || i == page_ptr2page_index(ro.allocator_ptr_1g)
            ||| i == page_ptr2page_index(container_ptr) || i == page_ptr2page_index(ro.pcid_allocator)
            ||| page_2m_tail_indices(page_ptr2page_index(container_ptr)).contains(i) || page_2m_tail_indices(page_ptr2page_index(ro.pcid_allocator)).contains(i)
        }),
{
    if index_valid(NUM_PAGES, i) && pre.pg_arr.spec_index(i).view().view().owning_container == container_ptr {
        kill_container_retire_eof_owned_page_at(pre, container_ptr, parent_ptr, owner_ptr, i);
    }
}
/// Before the retire, the retired container owns its object pages: its five 4K object pages hold its scheduler, cpu
/// set, and three allocators, its two 2M heads hold the container itself and its PCID allocator, and every tail of
/// those heads is merged. None of them is an I/O page.
pub proof fn kill_container_retire_eof_object_pages(pre: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr),
    ensures
        ({
            let ro = pre.ctn_mp.spec_index(container_ptr).view_rodata().view();
            let pages_4k = kill_container_retire_pages_4k(ro);
            let heads = kill_container_retire_heads(container_ptr, ro);
            &&& pages_4k[0] == page_ptr2page_index(ro.scheduler) && pages_4k[1] == page_ptr2page_index(ro.cpu_set) && pages_4k[2] == page_ptr2page_index(ro.allocator_ptr_4k)
            &&& pages_4k[3] == page_ptr2page_index(ro.allocator_ptr_2m) && pages_4k[4] == page_ptr2page_index(ro.allocator_ptr_1g) && pages_4k.len() == 5
            &&& heads[0] == page_ptr2page_index(container_ptr) && heads[1] == page_ptr2page_index(ro.pcid_allocator) && heads.len() == 2
            &&& page_ptr_valid(ro.scheduler) && page_ptr_valid(ro.cpu_set) && page_ptr_valid(ro.allocator_ptr_4k) && page_ptr_valid(ro.allocator_ptr_2m)
            &&& page_ptr_valid(ro.allocator_ptr_1g) && page_ptr_valid(container_ptr) && page_ptr_valid(ro.pcid_allocator)
            &&& forall|k: int| #![trigger pages_4k[k]] 0 <= k < 5 ==> {
                let page = pre.pg_arr.spec_index(pages_4k[k]).view().view();
                &&& index_valid(NUM_PAGES, pages_4k[k])
                &&& page.owning_container == container_ptr
                &&& !page.is_io_page
                &&& page.state is Allocated4k
            }
            &&& pre.pg_arr.spec_index(pages_4k[0]).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsScheduler })
            &&& pre.pg_arr.spec_index(pages_4k[1]).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet })
            &&& pre.pg_arr.spec_index(pages_4k[2]).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator })
            &&& pre.pg_arr.spec_index(pages_4k[3]).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator })
            &&& pre.pg_arr.spec_index(pages_4k[4]).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator })
            &&& forall|k: int| #![trigger heads[k]] 0 <= k < 2 ==> {
                let page = pre.pg_arr.spec_index(heads[k]).view().view();
                &&& page_index_2m_valid(heads[k])
                &&& page.owning_container == container_ptr
                &&& !page.is_io_page
                &&& page.state is Allocated2m
            }
            &&& pre.pg_arr.spec_index(heads[0]).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer })
            &&& pre.pg_arr.spec_index(heads[1]).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator })
            &&& forall|i: PageIndex| #![trigger pre.pg_arr.spec_index(i)] kill_container_retire_tails(heads).contains(i) ==> {
                let page = pre.pg_arr.spec_index(i).view().view();
                &&& index_valid(NUM_PAGES, i)
                &&& page.owning_container == container_ptr
                &&& !page.is_io_page
                &&& page.state is Merged2m
            }
        }),
{
    let ro = pre.ctn_mp.spec_index(container_ptr).view_rodata().view();
    let pages_4k = kill_container_retire_pages_4k(ro);
    let heads = kill_container_retire_heads(container_ptr, ro);
    page_ptr_roundtrip(); page_index_roundtrip();
    container_scheduler_wf_at(pre.ctn_mp, pre.sched_mp, container_ptr); container_cpu_set_wf_container_at(pre.ctn_mp, pre.cpu_set_mp, container_ptr);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, container_ptr); container_pcid_allocator_wf_container_at(pre.ctn_mp, pre.pcid_allc_mp, container_ptr);
    scheduler_pages_wf_at(pre.sched_mp, pre.pg_arr, ro.scheduler); cpu_set_pages_wf_at(pre.cpu_set_mp, pre.pg_arr, ro.cpu_set);
    allocator_4k_pages_wf_at(pre.pg_arr, pre.allc_4k_mp, ro.allocator_ptr_4k); allocator_2m_pages_wf_at(pre.pg_arr, pre.allc_2m_mp, ro.allocator_ptr_2m);
    allocator_1g_pages_wf_at(pre.pg_arr, pre.allc_1g_mp, ro.allocator_ptr_1g); pcid_allocator_pages_wf_at(pre.pg_arr, pre.pcid_allc_mp, ro.pcid_allocator);
    container_pages_backward_at(pre.pg_arr, pre.ctn_mp, container_ptr);
    assert(pages_4k[0] == page_ptr2page_index(ro.scheduler) && pages_4k[1] == page_ptr2page_index(ro.cpu_set) && pages_4k[2] == page_ptr2page_index(ro.allocator_ptr_4k)
        && pages_4k[3] == page_ptr2page_index(ro.allocator_ptr_2m) && pages_4k[4] == page_ptr2page_index(ro.allocator_ptr_1g));
    assert(heads[0] == page_ptr2page_index(container_ptr) && heads[1] == page_ptr2page_index(ro.pcid_allocator));
    let c0 = pre.pg_arr.spec_index(pages_4k[0]).view().view().owning_container;
    let c1 = pre.pg_arr.spec_index(pages_4k[1]).view().view().owning_container;
    let c2 = pre.pg_arr.spec_index(pages_4k[2]).view().view().owning_container;
    let c3 = pre.pg_arr.spec_index(pages_4k[3]).view().view().owning_container;
    let c4 = pre.pg_arr.spec_index(pages_4k[4]).view().view().owning_container;
    let c6 = pre.pg_arr.spec_index(heads[1]).view().view().owning_container;
    page_object_owner_wf_at(pre.pg_arr, pre.ctn_mp, pre.thr_mp, pages_4k[0]); container_page_owner_backward_at(pre.ctn_mp, pre.pg_arr, pages_4k[0]); container_scheduler_wf_at(pre.ctn_mp, pre.sched_mp, c0);
    page_object_owner_wf_at(pre.pg_arr, pre.ctn_mp, pre.thr_mp, pages_4k[1]); container_page_owner_backward_at(pre.ctn_mp, pre.pg_arr, pages_4k[1]); container_cpu_set_wf_container_at(pre.ctn_mp, pre.cpu_set_mp, c1);
    page_object_owner_wf_at(pre.pg_arr, pre.ctn_mp, pre.thr_mp, pages_4k[2]); container_page_owner_backward_at(pre.ctn_mp, pre.pg_arr, pages_4k[2]);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c2);
    page_object_owner_wf_at(pre.pg_arr, pre.ctn_mp, pre.thr_mp, pages_4k[3]); container_page_owner_backward_at(pre.ctn_mp, pre.pg_arr, pages_4k[3]);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c3);
    page_object_owner_wf_at(pre.pg_arr, pre.ctn_mp, pre.thr_mp, pages_4k[4]); container_page_owner_backward_at(pre.ctn_mp, pre.pg_arr, pages_4k[4]);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c4);
    page_object_owner_wf_at(pre.pg_arr, pre.ctn_mp, pre.thr_mp, heads[0]);
    page_object_owner_wf_at(pre.pg_arr, pre.ctn_mp, pre.thr_mp, heads[1]); container_page_owner_backward_at(pre.ctn_mp, pre.pg_arr, heads[1]);
    container_pcid_allocator_wf_container_at(pre.ctn_mp, pre.pcid_allc_mp, c6);
    page_array_wf_at(pre.pg_arr, pages_4k[0]); page_array_wf_at(pre.pg_arr, pages_4k[1]); page_array_wf_at(pre.pg_arr, pages_4k[2]); page_array_wf_at(pre.pg_arr, pages_4k[3]);
    page_array_wf_at(pre.pg_arr, pages_4k[4]); page_array_wf_at(pre.pg_arr, heads[0]); page_array_wf_at(pre.pg_arr, heads[1]);
    hugepage_2m_wf_head_at(pre.pg_arr, heads[0]); hugepage_2m_wf_head_at(pre.pg_arr, heads[1]);
    kill_container_retire_eof_tail_pages(pre, container_ptr, heads);
}
/// Every tail `i` of the 2M head `h` is a merged page with the head's owner and no I/O page.
broadcast proof fn kill_container_retire_eof_tail_page(page_array: PageLockedArray, h: PageIndex, i: PageIndex)
    requires
        page_array_wf(page_array),
        hugepage_2m_wf(page_array),
        page_index_2m_valid(h),
        page_array.spec_index(h).view().view().state is Allocated2m,
    ensures
        #![trigger page_2m_tail_indices(h).contains(i), page_array.spec_index(i)]
        page_2m_tail_indices(h).contains(i) ==> {
            let page = page_array.spec_index(i).view().view();
            &&& index_valid(NUM_PAGES, i)
            &&& page.owning_container == page_array.spec_index(h).view().view().owning_container
            &&& !page.is_io_page
            &&& page.state is Merged2m
        },
{
    if page_2m_tail_indices(h).contains(i) {
        assert(index_valid(NUM_PAGES, i) && spec_page_index_merge_2m_valid(h, i));
        hugepage_2m_wf_tail_at(page_array, h, i); page_array_wf_at(page_array, i);
    }
}

/// Every tail of the retired container's two 2M heads `heads`, which it owns, is a merged page it owns and no I/O page.
proof fn kill_container_retire_eof_tail_pages(pre: KernelK, container_ptr: RwLockContainerPtr, heads: Seq<PageIndex>)
    requires
        page_array_wf(pre.pg_arr),
        hugepage_2m_wf(pre.pg_arr),
        heads.len() == 2,
        forall|k: int| #![trigger heads[k]] 0 <= k < 2 ==> {
            let page = pre.pg_arr.spec_index(heads[k]).view().view();
            &&& page_index_2m_valid(heads[k])
            &&& page.owning_container == container_ptr
            &&& page.state is Allocated2m
        },
    ensures
        forall|i: PageIndex| #![trigger pre.pg_arr.spec_index(i)] kill_container_retire_tails(heads).contains(i) ==> {
            let page = pre.pg_arr.spec_index(i).view().view();
            &&& index_valid(NUM_PAGES, i)
            &&& page.owning_container == container_ptr
            &&& !page.is_io_page
            &&& page.state is Merged2m
        },
{
    assert(pre.pg_arr.spec_index(heads[0]).view().view().state is Allocated2m && pre.pg_arr.spec_index(heads[1]).view().view().state is Allocated2m);
    broadcast use kill_container_retire_eof_tail_page;
}
} // verus!
