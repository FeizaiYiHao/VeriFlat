use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub(super) open spec fn pop_stage_2m_page_transition_framing(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
) -> bool {
    let index = page_ptr2page_index(page);
    let old_page = pre.pg_arr.spec_index(index).view().view();
    let new_page = post.pg_arr.spec_index(index).view().view();
    let old_thread = pre.thr_mp.spec_index(thread);
    let new_thread = post.thr_mp.spec_index(thread);
    let old_allocator = pre.allc_2m_mp.spec_index(allocator);
    let new_allocator = post.allc_2m_mp.spec_index(allocator);
    let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
    &&& page_ptr_valid(page)
    &&& index_valid(NUM_PAGES, index)
    &&& pre.ctn_mp.dom().contains(container)
    &&& pre.ctn_mp.spec_index(container).view_rodata().view().allocator_ptr_2m == allocator
    &&& pre.thr_mp.dom().contains(thread)
    &&& thread_effective_quota_2m(old_thread) >= 1
    &&& old_thread.view().owning_container == container
    &&& pre.allc_2m_mp.dom().contains(allocator)
    &&& old_allocator.total_free_pages.view() > 0
    &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
    &&& old_page.free_list_node_storage.addr() == node
    &&& old_page.owning_container == container
    &&& !old_thread.view().temp_alloc_cache_2m.view().contains(page)
    &&& post == (KernelK { pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_2m_mp: post.allc_2m_mp, ..pre })
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, index)
    &&& new_page == (Page { state: PageState::Owned2m { thread_ptr: thread }, free_list_node_storage: new_page.free_list_node_storage, ..old_page })
    &&& new_page.free_list_node_storage.addr() == old_page.free_list_node_storage.addr()
    &&& new_page.free_list_node_storage.is_init()
    &&& post.pg_arr.spec_index(index).view().is_init()
    &&& post.pg_arr.spec_index(index).view().view_rodata() == pre.pg_arr.spec_index(index).view().view_rodata()
    &&& post.pg_arr.spec_index(index).view().view_ghost() == pre.pg_arr.spec_index(index).view().view_ghost()
    &&& post.pg_arr.spec_index(index).view().being_killed() == pre.pg_arr.spec_index(index).view().being_killed()
    &&& post.pg_arr.spec_index(index).view().locking_thread() is Write
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, thread)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] pre.thr_mp.dom().contains(t) ==>
        post.thr_mp.spec_index(t).view().temp_alloc_cache_4k == pre.thr_mp.spec_index(t).view().temp_alloc_cache_4k
        && post.thr_mp.spec_index(t).view().temp_alloc_cache_1g == pre.thr_mp.spec_index(t).view().temp_alloc_cache_1g
        && (t != thread ==> post.thr_mp.spec_index(t).view().temp_alloc_cache_2m == pre.thr_mp.spec_index(t).view().temp_alloc_cache_2m)
    &&& new_thread.view() == (Thread {
        temp_alloc_cache_2m: Ghost(old_thread.view().temp_alloc_cache_2m.view().insert(page)), ..old_thread.view()
    })
    &&& new_thread.is_init() == old_thread.is_init()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.locking_thread() is Write
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& post.allc_2m_mp.unchanged_except(&pre.allc_2m_mp, allocator)
    &&& new_allocator == (PageAllocator {
        cpu_caches: new_allocator.cpu_caches, global_pool: new_allocator.global_pool,
        total_free_pages: Ghost((old_allocator.total_free_pages.view() - 1) as usize), ..old_allocator
    })
    &&& match source {
        Some(cpu_id) => {
            let old_cache = old_allocator.cpu_caches.spec_index(cpu_id).view();
            let new_cache = new_allocator.cpu_caches.spec_index(cpu_id).view();
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& old_cache.view().linked_list.view().len() > 0
            &&& old_cache.view().linked_list.view().first() == page
            &&& old_cache.view().linked_list.map().dom().contains(node)
            &&& old_cache.view().linked_list.map().index(node) == page
            &&& new_allocator.global_pool == old_allocator.global_pool
            &&& new_allocator.cpu_caches.entries_unchanged_except(&old_allocator.cpu_caches, cpu_id)
            &&& new_cache.view().view() == old_cache.view().view().skip(1)
            &&& new_cache.view().map() == old_cache.view().map().remove(node)
            &&& new_cache.is_init()
            &&& new_cache.locking_thread() == old_cache.locking_thread()
            &&& new_cache.being_killed() == old_cache.being_killed()
            &&& new_allocator.cpu_caches.spec_index(cpu_id).lock_id() == old_allocator.cpu_caches.spec_index(cpu_id).lock_id()
        },
        None => {
            &&& old_allocator.global_pool.view().view().len() > 0
            &&& old_allocator.global_pool.view().view().first() == page
            &&& old_allocator.global_pool.view().map().dom().contains(node)
            &&& old_allocator.global_pool.view().map().index(node) == page
            &&& new_allocator.cpu_caches == old_allocator.cpu_caches
            &&& new_allocator.global_pool.view().view() == old_allocator.global_pool.view().view().skip(1)
            &&& new_allocator.global_pool.view().map() == old_allocator.global_pool.view().map().remove(node)
            &&& new_allocator.global_pool.is_init() == old_allocator.global_pool.is_init()
            &&& new_allocator.global_pool.lock_id() == old_allocator.global_pool.lock_id()
            &&& new_allocator.global_pool.locking_thread() == old_allocator.global_pool.locking_thread()
            &&& new_allocator.global_pool.being_killed() == old_allocator.global_pool.being_killed()
        },
    }
}

proof fn eof_pop_2m_subsystems_inv(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.pg_arr.inv(),
        post.thr_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_2m_mp.spec_index(allocator).wf(),
    ensures post.subsystems_inv(),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_array_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf); reveal(allocator_perms_wf); reveal(process_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(page_array_wf); reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
}

proof fn eof_pop_2m_cpu_set_pages(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
}

proof fn eof_pop_2m_allocator_2m_pages(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures allocator_2m_pages_wf(post.pg_arr, post.allc_2m_mp),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(allocator_2m_pages_wf(post.pg_arr, post.allc_2m_mp)) by { reveal(allocator_2m_pages_wf); };
}

proof fn eof_pop_2m_allocator_4k_pages(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures allocator_4k_pages_wf(post.pg_arr, post.allc_4k_mp),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(allocator_4k_pages_wf(post.pg_arr, post.allc_4k_mp)) by { reveal(allocator_4k_pages_wf); };
}

proof fn eof_pop_2m_allocator_1g_pages(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures allocator_1g_pages_wf(post.pg_arr, post.allc_1g_mp),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(allocator_1g_pages_wf(post.pg_arr, post.allc_1g_mp)) by { reveal(allocator_1g_pages_wf); };
}

proof fn eof_pop_2m_container_page_owner(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures container_page_owner_wf(post.ctn_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_page_owner_wf); };
}

proof fn eof_pop_2m_container_process_page_pagetable(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
}

proof fn eof_pop_2m_container_pages(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures container_pages_wf(post.pg_arr, post.ctn_mp),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { reveal(container_pages_wf); };
}

proof fn eof_pop_2m_process_pages(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures process_pages_wf(post.pg_arr, post.prc_mp),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { reveal(process_pages_wf); };
}

proof fn eof_pop_2m_quota(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures
        container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp),
        container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp),
        container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
        reveal(container_process_allocator_quota_2m_wf); reveal(container_process_wf); reveal(container_thread_wf); reveal(container_allocator_wf);
        lemma_thread_effective_quota_2m_fold_change_by_forall(thread, -1);
        lemma_thread_effective_quota_2m_fold_sum_eq_forall();
        lemma_thread_pending_2m_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        lemma_process_effective_quota_2m_fold_sum_eq_forall();
    };
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_thread_wf); lemma_thread_effective_quota_4k_fold_sum_eq_forall(); lemma_thread_pending_4k_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp); };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by { reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf); lemma_thread_effective_quota_1g_fold_sum_eq_forall(); lemma_thread_pending_1g_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp); };
}

proof fn eof_pop_2m_page_types(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_pagetable_wf(post.pt_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_2m_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_1g_wf(post.pg_arr)) by { reveal(hugepage_1g_wf); };
    assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
}

proof fn eof_pop_2m_staged_pages(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures
        thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
    assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
        assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
        assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_1g_wf); };
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
}

proof fn eof_pop_2m_global_pool(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures container_allocator_global_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
{
    hide(Seq::contains);
    reveal(pop_stage_2m_page_transition_framing);
    if source is Some {
        assert(container_allocator_global_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by {
            reveal(allocator_perms_wf); reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf);
            page_ptr_valid_imply_page_index_valid();
        };
    } else {
        assert(container_allocator_global_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by {
            page_ptr2page_index_injective();
            reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); reveal(allocator_perms_wf);
            reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list);
            seq_skip_lemma::<PagePtr>();
        };
    }
}

proof fn eof_pop_2m_cpu_cache(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures container_allocator_cpu_cache_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
{
    hide(Seq::contains);
    reveal(pop_stage_2m_page_transition_framing);
    if source is Some {
        assert(container_allocator_cpu_cache_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by {
            reveal(allocator_perms_wf);
            page_ptr_roundtrip();
            reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf);
            reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list);
            seq_skip_lemma::<PagePtr>();
        };
    } else {
        assert(container_allocator_cpu_cache_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by {
            reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf);
            page_ptr_valid_imply_page_index_valid();
            page_ptr2page_index_injective();
            reveal(allocator_perms_wf);
        };
    }
}

proof fn eof_pop_2m_free_pages(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures
        post.allocator_free_pages_wf(),
        container_allocator_global_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_cpu_cache_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_cpu_cache_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_global_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
        container_allocator_cpu_cache_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(post.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
    eof_pop_2m_global_pool(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_cpu_cache(pre, post, allocator, thread, container, page, node, source);
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); };
    assert(container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_cpu_cache_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); };
    assert(container_allocator_global_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_cpu_cache_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); };
}

proof fn eof_pop_2m_memory_management_inv(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    eof_pop_2m_cpu_set_pages(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_allocator_2m_pages(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_allocator_4k_pages(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_allocator_1g_pages(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_container_page_owner(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_container_process_page_pagetable(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_container_pages(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_process_pages(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_quota(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_page_types(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_staged_pages(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_free_pages(pre, post, allocator, thread, container, page, node, source);
}

proof fn eof_pop_2m_process_management_inv(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(pop_stage_2m_page_transition_framing);
    assert(post.process_management_inv()) by {
        assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
        assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_thread_endpoint_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { reveal(container_thread_scheduler_wf); };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
    };
}

pub(super) proof fn pop_stage_2m_page_eof(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
)
    requires
        pre.inv(),
        pop_stage_2m_page_transition_framing(pre, post, allocator, thread, container, page, node, source),
        post.pg_arr.inv(),
        post.thr_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_2m_mp.spec_index(allocator).wf(),
    ensures post.inv(),
{
    reveal(pop_stage_2m_page_transition_framing);
    eof_pop_2m_subsystems_inv(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_memory_management_inv(pre, post, allocator, thread, container, page, node, source);
    eof_pop_2m_process_management_inv(pre, post, allocator, thread, container, page, node, source);
}
}
