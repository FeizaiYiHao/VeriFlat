use vstd::prelude::*;
use crate::*;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_alloc_page::free_4k_page::kill_container_quota_fold::lemma_container_allocator_quota_eq_total_free_without_users;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::free_4k_page::kill_container_quota_fold::lemma_container_allocator_quota_eq_total_free_without_users;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_spec::*;

verus! {
/// The retired container `ctn_ptr` is marked and childless, has parent `parent_ptr` and `owner_ptr` in its upper
/// tree, owns no process, thread, indirect thread, or cpu, and has zero quotas.
pub(crate) open spec fn kill_container_retire_eof_target_empty(pre: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr) -> bool {
    let target = pre.ctn_mp.spec_index(ctn_ptr);
    let ro = target.view_rodata().view();
    &&& pre.ctn_mp.dom().contains(ctn_ptr)
    &&& pre.ctn_mp.dom().contains(parent_ptr)
    &&& pre.ctn_mp.dom().contains(owner_ptr)
    &&& owner_ptr != ctn_ptr
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
pub(crate) broadcast proof fn kill_container_retire_eof_subtree_empty(pre: KernelK, ctn_ptr: RwLockContainerPtr, sub: RwLockContainerPtr)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view().children.view().len() == 0,
    ensures !(#[trigger] pre.ctn_mp.spec_index(ctn_ptr).view_ghost().subtree_set.view().contains(sub)),
{
    if pre.ctn_mp.spec_index(ctn_ptr).view_ghost().subtree_set.view().contains(sub) {
        let d = pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth;
        let uppers = pre.ctn_mp.spec_index(sub).view_ghost().uppertree_seq.view();
        assert(pre.ctn_mp.dom().contains(sub) && uppers.len() > d && uppers[d as int] == ctn_ptr) by { reveal(container_subtree_set_wf); };
        container_perms_wf_at(pre.ctn_mp, ctn_ptr); container_perms_wf_at(pre.ctn_mp, sub);
        let x = if uppers.len() == d + 1 { sub } else { uppers[d + 1] };
        if uppers.len() != d + 1 {
            assert(uppers.contains(x));
            container_uppertree_seq_wf_at(pre.rt_ctn, pre.ctn_mp, sub, x); container_perms_wf_at(pre.ctn_mp, x);
        }
        assert(pre.ctn_mp.dom().contains(x));
        assert(pre.ctn_mp.spec_index(x).view_rodata().view().depth == d + 1);
        assert(pre.ctn_mp.spec_index(x).view_ghost().uppertree_seq.view()[d as int] == ctn_ptr);
        container_root_wf_at(pre.rt_ctn, pre.ctn_mp, x);
        assert(pre.ctn_mp.spec_index(x).view_rodata().view().parent == Some(ctn_ptr)) by { reveal(container_uppertree_seq_parent_wf); };
        assert(pre.ctn_mp.spec_index(ctn_ptr).view().children.view().contains(x)) by { reveal(container_children_parent_wf); };
    }
}

/// An endpoint whose owner is a childless container without threads has no holder `m`: every holder of an endpoint
/// lives in its owner's subtree.
pub(crate) broadcast proof fn kill_container_retire_eof_no_endpoint_holder(pre: KernelK, e: RwLockEndpointPtr, m: (RwLockThreadPtr, EndpointIdx))
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
pub(crate) broadcast proof fn kill_container_retire_eof_no_endpoint(pre: KernelK, ctn_ptr: RwLockContainerPtr, e: RwLockEndpointPtr)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view().children.view().len() == 0,
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
    ensures !(#[trigger] pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_endpoints.view().contains(e)),
{
    if pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_endpoints.view().contains(e) {
        assert(pre.ep_mp.dom().contains(e) && pre.ep_mp.spec_index(e).view().owning_container == ctn_ptr) by { reveal(container_endpoint_wf); };
        let endpoint = pre.ep_mp.spec_index(e).view();
        reveal(endpoint_perms_wf);
        assert(endpoint.rf_counter == endpoint.owning_threads.view().len() && endpoint.rf_counter != 0);
        assert(endpoint.owning_threads.view() =~= Set::<(RwLockThreadPtr, EndpointIdx)>::empty()) by { broadcast use kill_container_retire_eof_no_endpoint_holder; };
    }
}

/// A mapped page whose owner is a childless container without processes records no page-table or IOMMU mapping `m`:
/// every mapping belongs to a process in its owner's subtree.
pub(crate) broadcast proof fn kill_container_retire_eof_no_mapping(pre: KernelK, i: PageIndex, m: (RwLockPageTableRoot, VAddr))
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
    container_owned_pages_wf_backward_at(pre.ctn_mp, pre.pg_arr, i);
    assert(!pre.pg_arr.spec_index(i).view().view().mappings().contains((table, va))) by {
        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); broadcast use kill_container_retire_eof_subtree_empty;
    };
    assert(!pre.pg_arr.spec_index(i).view().view().iommu_mappings().contains((table, va))) by {
        reveal(page_iommu_table_wf); reveal(container_process_wf); broadcast use kill_container_retire_eof_subtree_empty;
    };
}

/// A page owned by a childless container without processes is not mapped.
proof fn kill_container_retire_eof_no_mapped_page_at(pre: KernelK, ctn_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view().children.view().len() == 0,
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == ctn_ptr,
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
proof fn kill_container_retire_eof_no_process_page_at(pre: KernelK, ctn_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == ctn_ptr,
    ensures !page_state_is_process_kernel_page(pre.pg_arr.spec_index(i).view().view().state),
{
    let state = pre.pg_arr.spec_index(i).view().view().state;
    if page_state_is_process_kernel_page(state) {
        process_object_pages_owner_wf_at(pre.prc_mp, pre.pt_mp, pre.it_mp, pre.pg_arr, i);
        reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(container_process_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
        if state->Allocated4k_state is AsPageTableRoot {
            assert(state->Allocated4k_state->AsPageTableRoot_table_type == PT_TYPE || state->Allocated4k_state->AsPageTableRoot_table_type == IOMMU_TYPE);
        } else if state->Allocated4k_state is PageTable {
            assert(state->Allocated4k_state->PageTable_table_type == PT_TYPE || state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE);
        }
    }
}

/// A page owned by a container without processes, threads, or indirect threads and with zero 4K quota is not a free
/// 4K page: its 4K allocator holds no free page.
proof fn kill_container_retire_eof_no_free_4k_page_at(pre: KernelK, ctn_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value == 0,
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == ctn_ptr,
    ensures !(pre.pg_arr.spec_index(i).view().view().state is Free4k),
{
    let page = pre.pg_arr.spec_index(i).view().view();
    if page.state is Free4k {
        lemma_container_allocator_quota_eq_total_free_without_users(pre, ctn_ptr);
        allocator_free_4k_pages_wf_at(pre.allc_4k_mp, pre.pg_arr, i);
        let a = page.state->Free4k_allocator_ptr.view();
        assert(pre.allc_4k_mp.dom().contains(a) && pre.allc_4k_mp.spec_index(a).owning_container == ctn_ptr);
        assert(a == pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k) by { reveal(container_allocator_wf); };
        let allocator = pre.allc_4k_mp.spec_index(a);
        allocator_perms_wf_at(pre.allc_4k_mp, a);
        if page.state->Free4k_state is PreCpuCache {
            let cpu = page.state->Free4k_state->PreCpuCache_cpu_id;
            allocator.cpu_caches.view_index_eq_element_value(); lemma_cache_len_fold_ge_elem(allocator.cpu_caches.view(), cpu as int);
            allocator.cpu_caches.spec_index(cpu).view().view().linked_list.wf_implies_view_len_eq_len();
        } else {
            lemma_cache_len_fold_nonneg(allocator.cpu_caches.view()); allocator.global_pool.view().wf_implies_view_len_eq_len();
        }
    }
}

/// A page owned by a container without processes, threads, or indirect threads and with zero 2M quota is not a free
/// 2M page: its 2M allocator holds no free page.
proof fn kill_container_retire_eof_no_free_2m_page_at(pre: KernelK, ctn_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_2m).quota.view().value == 0,
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == ctn_ptr,
    ensures !(pre.pg_arr.spec_index(i).view().view().state is Free2m),
{
    let page = pre.pg_arr.spec_index(i).view().view();
    if page.state is Free2m {
        lemma_container_allocator_quota_eq_total_free_without_users(pre, ctn_ptr);
        allocator_free_2m_pages_wf_at(pre.allc_2m_mp, pre.pg_arr, i);
        let a = page.state->Free2m_allocator_ptr.view();
        assert(pre.allc_2m_mp.dom().contains(a) && pre.allc_2m_mp.spec_index(a).owning_container == ctn_ptr);
        assert(a == pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_2m) by { reveal(container_allocator_wf); };
        let allocator = pre.allc_2m_mp.spec_index(a);
        allocator_perms_wf_at(pre.allc_2m_mp, a);
        if page.state->Free2m_state is PreCpuCache {
            let cpu = page.state->Free2m_state->PreCpuCache_cpu_id;
            allocator.cpu_caches.view_index_eq_element_value(); lemma_cache_len_fold_ge_elem(allocator.cpu_caches.view(), cpu as int);
            allocator.cpu_caches.spec_index(cpu).view().view().linked_list.wf_implies_view_len_eq_len();
        } else {
            lemma_cache_len_fold_nonneg(allocator.cpu_caches.view()); allocator.global_pool.view().wf_implies_view_len_eq_len();
        }
    }
}

/// A page owned by a container without processes, threads, or indirect threads and with zero 1G quota is not a free
/// 1G page: its 1G allocator holds no free page.
proof fn kill_container_retire_eof_no_free_1g_page_at(pre: KernelK, ctn_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_1g).quota.view().value == 0,
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == ctn_ptr,
    ensures !(pre.pg_arr.spec_index(i).view().view().state is Free1g),
{
    let page = pre.pg_arr.spec_index(i).view().view();
    if page.state is Free1g {
        lemma_container_allocator_quota_eq_total_free_without_users(pre, ctn_ptr);
        let a = page.state->Free1g_allocator_ptr.view();
        let ptr = page_index2page_ptr(i);
        if page.state->Free1g_state is PreCpuCache {
            let cpu = page.state->Free1g_state->PreCpuCache_cpu_id;
            assert(index_valid(NUM_CPUS, cpu) && pre.allc_1g_mp.dom().contains(a) && pre.allc_1g_mp.spec_index(a).owning_container == ctn_ptr
                && pre.allc_1g_mp.spec_index(a).cpu_caches.spec_index(cpu).view().view().view().contains(ptr)) by {
                reveal(allocator_free_1g_pages_wf); reveal(allocator_cpu_cache_1g_pages_wf);
            };
        } else {
            assert(pre.allc_1g_mp.dom().contains(a) && pre.allc_1g_mp.spec_index(a).owning_container == ctn_ptr && pre.allc_1g_mp.spec_index(a).global_pool.view().view().contains(ptr)) by {
                reveal(allocator_free_1g_pages_wf); reveal(allocator_global_pool_1g_pages_wf);
            };
        }
        assert(a == pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_1g) by { reveal(container_allocator_wf); };
        let allocator = pre.allc_1g_mp.spec_index(a);
        allocator_perms_wf_at(pre.allc_1g_mp, a);
        if page.state->Free1g_state is PreCpuCache {
            let cpu = page.state->Free1g_state->PreCpuCache_cpu_id;
            allocator.cpu_caches.view_index_eq_element_value(); lemma_cache_len_fold_ge_elem(allocator.cpu_caches.view(), cpu as int);
            allocator.cpu_caches.spec_index(cpu).view().view().linked_list.wf_implies_view_len_eq_len();
        } else {
            lemma_cache_len_fold_nonneg(allocator.cpu_caches.view()); allocator.global_pool.view().wf_implies_view_len_eq_len();
        }
    }
}

/// A page owned by a container without processes, threads, indirect threads, or quota is not free.
proof fn kill_container_retire_eof_no_free_page_at(pre: KernelK, ctn_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty(),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty(),
        pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value == 0,
        pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_2m).quota.view().value == 0,
        pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_1g).quota.view().value == 0,
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == ctn_ptr,
    ensures !pre.pg_arr.spec_index(i).view().view().is_free(),
{
    kill_container_retire_eof_no_free_4k_page_at(pre, ctn_ptr, i); kill_container_retire_eof_no_free_2m_page_at(pre, ctn_ptr, i);
    kill_container_retire_eof_no_free_1g_page_at(pre, ctn_ptr, i);
}

/// A 2M head page owned by the retired container is one of its two 2M object pages.
proof fn kill_container_retire_eof_owned_head_2m_at(pre: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == ctn_ptr,
        page_state_2m_related(pre.pg_arr.spec_index(i).view().view().state),
        !pre.pg_arr.spec_index(i).view().view().is_merged(),
    ensures
        i == page_ptr2page_index(ctn_ptr) || i == page_ptr2page_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator),
{
    let state = pre.pg_arr.spec_index(i).view().view().state;
    kill_container_retire_eof_no_free_page_at(pre, ctn_ptr, i); kill_container_retire_eof_no_mapped_page_at(pre, ctn_ptr, i);
    page_object_owner_wf_at(pre.ctn_mp, pre.thrd_mp, pre.pg_arr, i); page_index_roundtrip();
    if state is Owned2m { container_thread_wf_thread_at(pre.ctn_mp, pre.thrd_mp, state->Owned2m_thread_ptr); }
    assert(state is Allocated2m);
    assert(state->Allocated2m_state is AsContainer || state->Allocated2m_state is AsPcidAllocator);
}

/// A non-merged page the retired container `ctn_ptr` owns is one of its five 4K or two 2M object pages.
proof fn kill_container_retire_eof_owned_page_at(pre: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
        index_valid(NUM_PAGES, i),
        pre.pg_arr.spec_index(i).view().view().owning_container == ctn_ptr,
        !pre.pg_arr.spec_index(i).view().view().is_merged(),
    ensures
        ({
            let ro = pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view();
            ||| i == page_ptr2page_index(ro.scheduler) || i == page_ptr2page_index(ro.cpu_set) || i == page_ptr2page_index(ro.allocator_ptr_4k)
            ||| i == page_ptr2page_index(ro.allocator_ptr_2m) || i == page_ptr2page_index(ro.allocator_ptr_1g)
            ||| i == page_ptr2page_index(ctn_ptr) || i == page_ptr2page_index(ro.pcid_allocator)
        }),
{
    let state = pre.pg_arr.spec_index(i).view().view().state;
    page_index_roundtrip();
    page_object_owner_wf_at(pre.ctn_mp, pre.thrd_mp, pre.pg_arr, i);
    kill_container_retire_eof_no_free_page_at(pre, ctn_ptr, i); kill_container_retire_eof_no_mapped_page_at(pre, ctn_ptr, i);
    kill_container_retire_eof_no_process_page_at(pre, ctn_ptr, i);
    if state is Owned4k || state is Owned2m || state is Owned1g {
        let t = if state is Owned4k { state->Owned4k_thread_ptr } else if state is Owned2m { state->Owned2m_thread_ptr } else { state->Owned1g_thread_ptr };
        container_thread_wf_thread_at(pre.ctn_mp, pre.thrd_mp, t);
    }
    if state is Allocated2m {
        kill_container_retire_eof_owned_head_2m_at(pre, ctn_ptr, parent_ptr, owner_ptr, i);
    } else if state is Allocated4k {
        assert(state->Allocated4k_state is AsEndpoint ==> pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_endpoints.view().contains(page_index2page_ptr(i)));
        kill_container_retire_eof_no_endpoint(pre, ctn_ptr, page_index2page_ptr(i));
    }
}

/// Every non-merged page the retired container `ctn_ptr` owns is one of its object pages.
pub(crate) broadcast proof fn kill_container_retire_eof_owned_page(pre: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, i: PageIndex)
    requires
        pre.inv(),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures
        #![trigger kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr), pre.pg_arr.spec_index(i).view().view().owning_container]
        index_valid(NUM_PAGES, i) && pre.pg_arr.spec_index(i).view().view().owning_container == ctn_ptr && !pre.pg_arr.spec_index(i).view().view().is_merged() ==> ({
            let ro = pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view();
            ||| i == page_ptr2page_index(ro.scheduler) || i == page_ptr2page_index(ro.cpu_set) || i == page_ptr2page_index(ro.allocator_ptr_4k)
            ||| i == page_ptr2page_index(ro.allocator_ptr_2m) || i == page_ptr2page_index(ro.allocator_ptr_1g)
            ||| i == page_ptr2page_index(ctn_ptr) || i == page_ptr2page_index(ro.pcid_allocator)
        }),
{
    if index_valid(NUM_PAGES, i) && pre.pg_arr.spec_index(i).view().view().owning_container == ctn_ptr && !pre.pg_arr.spec_index(i).view().view().is_merged() {
        kill_container_retire_eof_owned_page_at(pre, ctn_ptr, parent_ptr, owner_ptr, i);
    }
}
/// The retired container owns its object pages: five 4K pages for its scheduler, cpu set, and allocators and two 2M heads for itself and its PCID allocator, none an I/O page.
pub(crate) proof fn kill_container_retire_eof_object_pages(pre: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures
        ({
            let ro = pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view();
            let pages_4k = kill_container_retire_pages_4k(ro);
            let heads = kill_container_retire_heads(ctn_ptr, ro);
            &&& pages_4k[0] == page_ptr2page_index(ro.scheduler) && pages_4k[1] == page_ptr2page_index(ro.cpu_set) && pages_4k[2] == page_ptr2page_index(ro.allocator_ptr_4k)
            &&& pages_4k[3] == page_ptr2page_index(ro.allocator_ptr_2m) && pages_4k[4] == page_ptr2page_index(ro.allocator_ptr_1g) && pages_4k.len() == 5
            &&& heads[0] == page_ptr2page_index(ctn_ptr) && heads[1] == page_ptr2page_index(ro.pcid_allocator) && heads.len() == 2
            &&& page_ptr_valid(ro.scheduler) && page_ptr_valid(ro.cpu_set) && page_ptr_valid(ro.allocator_ptr_4k) && page_ptr_valid(ro.allocator_ptr_2m)
            &&& page_ptr_valid(ro.allocator_ptr_1g) && page_ptr_valid(ctn_ptr) && page_ptr_valid(ro.pcid_allocator)
            &&& forall|k: int| #![trigger pages_4k[k]] 0 <= k < 5 ==> {
                let page = pre.pg_arr.spec_index(pages_4k[k]).view().view();
                &&& index_valid(NUM_PAGES, pages_4k[k])
                &&& page.owning_container == ctn_ptr
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
                &&& page.owning_container == ctn_ptr
                &&& !page.is_io_page
                &&& page.state is Allocated2m
            }
            &&& pre.pg_arr.spec_index(heads[0]).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer })
            &&& pre.pg_arr.spec_index(heads[1]).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator })
        }),
{
    let ro = pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view();
    let pages_4k = kill_container_retire_pages_4k(ro);
    let heads = kill_container_retire_heads(ctn_ptr, ro);
    page_ptr_roundtrip(); page_index_roundtrip();
    container_scheduler_wf_container_at(pre.ctn_mp, pre.sched_mp, ctn_ptr); container_cpu_set_wf_container_at(pre.ctn_mp, pre.cpu_set_mp, ctn_ptr);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, ctn_ptr); container_pcid_allocator_wf_container_at(pre.ctn_mp, pre.pcid_allc_mp, ctn_ptr);
    scheduler_pages_wf_at(pre.sched_mp, pre.pg_arr, ro.scheduler); cpu_set_pages_wf_at(pre.cpu_set_mp, pre.pg_arr, ro.cpu_set);
    allocator_4k_pages_wf_at(pre.allc_4k_mp, pre.pg_arr, ro.allocator_ptr_4k); allocator_2m_pages_wf_at(pre.allc_2m_mp, pre.pg_arr, ro.allocator_ptr_2m);
    allocator_1g_pages_wf_at(pre.allc_1g_mp, pre.pg_arr, ro.allocator_ptr_1g); pcid_allocator_pages_wf_at(pre.pcid_allc_mp, pre.pg_arr, ro.pcid_allocator);
    container_pages_wf_container_at(pre.ctn_mp, pre.pg_arr, ctn_ptr);
    assert(pages_4k[0] == page_ptr2page_index(ro.scheduler) && pages_4k[1] == page_ptr2page_index(ro.cpu_set) && pages_4k[2] == page_ptr2page_index(ro.allocator_ptr_4k)
        && pages_4k[3] == page_ptr2page_index(ro.allocator_ptr_2m) && pages_4k[4] == page_ptr2page_index(ro.allocator_ptr_1g));
    assert(heads[0] == page_ptr2page_index(ctn_ptr) && heads[1] == page_ptr2page_index(ro.pcid_allocator));
    let c0 = pre.pg_arr.spec_index(pages_4k[0]).view().view().owning_container;
    let c1 = pre.pg_arr.spec_index(pages_4k[1]).view().view().owning_container;
    let c2 = pre.pg_arr.spec_index(pages_4k[2]).view().view().owning_container;
    let c3 = pre.pg_arr.spec_index(pages_4k[3]).view().view().owning_container;
    let c4 = pre.pg_arr.spec_index(pages_4k[4]).view().view().owning_container;
    let c6 = pre.pg_arr.spec_index(heads[1]).view().view().owning_container;
    page_object_owner_wf_at(pre.ctn_mp, pre.thrd_mp, pre.pg_arr, pages_4k[0]); container_owned_pages_wf_backward_at(pre.ctn_mp, pre.pg_arr, pages_4k[0]); container_scheduler_wf_container_at(pre.ctn_mp, pre.sched_mp, c0);
    page_object_owner_wf_at(pre.ctn_mp, pre.thrd_mp, pre.pg_arr, pages_4k[1]); container_owned_pages_wf_backward_at(pre.ctn_mp, pre.pg_arr, pages_4k[1]); container_cpu_set_wf_container_at(pre.ctn_mp, pre.cpu_set_mp, c1);
    page_object_owner_wf_at(pre.ctn_mp, pre.thrd_mp, pre.pg_arr, pages_4k[2]); container_owned_pages_wf_backward_at(pre.ctn_mp, pre.pg_arr, pages_4k[2]);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c2);
    page_object_owner_wf_at(pre.ctn_mp, pre.thrd_mp, pre.pg_arr, pages_4k[3]); container_owned_pages_wf_backward_at(pre.ctn_mp, pre.pg_arr, pages_4k[3]);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c3);
    page_object_owner_wf_at(pre.ctn_mp, pre.thrd_mp, pre.pg_arr, pages_4k[4]); container_owned_pages_wf_backward_at(pre.ctn_mp, pre.pg_arr, pages_4k[4]);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, c4);
    page_object_owner_wf_at(pre.ctn_mp, pre.thrd_mp, pre.pg_arr, heads[0]);
    page_object_owner_wf_at(pre.ctn_mp, pre.thrd_mp, pre.pg_arr, heads[1]); container_owned_pages_wf_backward_at(pre.ctn_mp, pre.pg_arr, heads[1]);
    container_pcid_allocator_wf_container_at(pre.ctn_mp, pre.pcid_allc_mp, c6);
    page_array_wf_at(pre.pg_arr, pages_4k[0]); page_array_wf_at(pre.pg_arr, pages_4k[1]); page_array_wf_at(pre.pg_arr, pages_4k[2]); page_array_wf_at(pre.pg_arr, pages_4k[3]);
    page_array_wf_at(pre.pg_arr, pages_4k[4]); page_array_wf_at(pre.pg_arr, heads[0]); page_array_wf_at(pre.pg_arr, heads[1]);
    hugepage_2m_wf_head_at(pre.pg_arr, heads[0]); hugepage_2m_wf_head_at(pre.pg_arr, heads[1]);
}
} // verus!
