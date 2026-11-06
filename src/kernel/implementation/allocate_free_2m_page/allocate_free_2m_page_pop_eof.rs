use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub(super) open spec fn pop_stage_2m_page_eof_transition_framing(
    pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr,
    container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>,
) -> bool {
    let index = page_ptr2page_index(page);
    let old_page = pre.pg_arr.spec_index(index).view().view();
    let new_page = post.pg_arr.spec_index(index).view().view();
    let old_thread = pre.thrd_mp.spec_index(thread);
    let new_thread = post.thrd_mp.spec_index(thread);
    let old_allocator = pre.allc_2m_mp.spec_index(allocator);
    let new_allocator = post.allc_2m_mp.spec_index(allocator);
    &&& post == (KernelK { pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, allc_2m_mp: post.allc_2m_mp, ..pre })
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, index)
    &&& new_page == (Page { state: PageState::Owned2m { thread_ptr: thread }, free_list_node_storage: new_page.free_list_node_storage, ..old_page })
    &&& new_page.free_list_node_storage.addr() == old_page.free_list_node_storage.addr()
    &&& new_page.free_list_node_storage.is_init()
    &&& post.pg_arr.spec_index(index).view().is_init()
    &&& post.pg_arr.spec_index(index).view().view_rodata() == pre.pg_arr.spec_index(index).view().view_rodata()
    &&& post.pg_arr.spec_index(index).view().view_ghost() == pre.pg_arr.spec_index(index).view().view_ghost()
    &&& post.pg_arr.spec_index(index).view().being_killed() == pre.pg_arr.spec_index(index).view().being_killed()
    &&& post.pg_arr.spec_index(index).view().locking_thread() is Write
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, thread)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thrd_mp.spec_index(t)] pre.thrd_mp.dom().contains(t) ==>
        post.thrd_mp.spec_index(t).view().temp_alloc_cache_4k == pre.thrd_mp.spec_index(t).view().temp_alloc_cache_4k
        && post.thrd_mp.spec_index(t).view().temp_alloc_cache_1g == pre.thrd_mp.spec_index(t).view().temp_alloc_cache_1g
        && (t != thread ==> post.thrd_mp.spec_index(t).view().temp_alloc_cache_2m == pre.thrd_mp.spec_index(t).view().temp_alloc_cache_2m)
        && post.thrd_mp.spec_index(t).view().endpoint_descriptors == pre.thrd_mp.spec_index(t).view().endpoint_descriptors
    &&& new_thread.view() == (Thread { temp_alloc_cache_2m: Ghost(old_thread.view().temp_alloc_cache_2m.view().insert(page)), ..old_thread.view() })
    &&& new_thread.is_init() == old_thread.is_init()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.locking_thread() is Write
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& post.allc_2m_mp.unchanged_except(&pre.allc_2m_mp, allocator)
    &&& new_allocator == (PageAllocator { cpu_caches: new_allocator.cpu_caches, global_pool: new_allocator.global_pool, total_free_pages: Ghost((old_allocator.total_free_pages.view() - 1) as usize), ..old_allocator })
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

proof fn pop_stage_2m_page_eof_subsystems_inv(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let old_thread = pre.thrd_mp.spec_index(thread);
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& page_ptr_valid(page)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& pre.ctn_mp.dom().contains(container)
            &&& pre.ctn_mp.spec_index(container).view_rodata().view().allocator_ptr_2m == allocator
            &&& pre.thrd_mp.dom().contains(thread)
            &&& thread_effective_quota_2m(old_thread) >= 1
            &&& old_thread.view().owning_container == container
            &&& pre.allc_2m_mp.dom().contains(allocator)
            &&& pre.allc_2m_mp.spec_index(allocator).total_free_pages.view() > 0
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
            &&& old_page.free_list_node_storage.addr() == node
            &&& old_page.owning_container == container
            &&& !old_thread.view().temp_alloc_cache_2m.view().contains(page)
        }),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_2m_mp.spec_index(allocator).wf(),
    ensures post.subsystems_inv(),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(post.subsystems_inv()) by {
        reveal(KernelK::default_pagetable_wf); reveal(allocator_perms_wf);
        reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked); reveal(page_array_wf); reveal(Page::mappings_va_valid); reveal(thread_perms_wf);
        reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_ipc_transit_wf);
    };
}

proof fn pop_stage_2m_page_eof_cpu_set_pages(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
        }),
        post.subsystems_inv(),
    ensures cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
}

proof fn pop_stage_2m_page_eof_allocator_2m_pages(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
        }),
        post.subsystems_inv(),
    ensures allocator_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(allocator_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_2m_pages_wf); page_ptr_roundtrip(); };
}

proof fn pop_stage_2m_page_eof_allocator_4k_pages(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
        }),
        post.subsystems_inv(),
    ensures allocator_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(allocator_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_4k_pages_wf); };
}

proof fn pop_stage_2m_page_eof_allocator_1g_pages(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
        }),
        post.subsystems_inv(),
    ensures allocator_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(allocator_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(allocator_1g_pages_wf); };
}

proof fn pop_stage_2m_page_eof_container_page_owner(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& pre.ctn_mp.dom().contains(container)
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
            &&& old_page.owning_container == container
        }),
        post.subsystems_inv(),
    ensures container_owned_pages_wf(post.ctn_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
}

proof fn pop_stage_2m_page_eof_container_process_page_pagetable(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
        }),
        post.subsystems_inv(),
    ensures
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
}

proof fn pop_stage_2m_page_eof_container_pages(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& pre.ctn_mp.dom().contains(container)
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
            &&& old_page.owning_container == container
        }),
        post.subsystems_inv(),
    ensures container_pages_wf(post.ctn_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_pages_wf); };
}

proof fn pop_stage_2m_page_eof_process_pages(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
        }),
        post.subsystems_inv(),
    ensures
        process_pages_wf(post.prc_mp, post.pg_arr),
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { reveal(process_pages_wf); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
}

proof fn pop_stage_2m_page_eof_page_object_owner(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        page_object_owner_wf(pre.ctn_mp, pre.thrd_mp, pre.pg_arr),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
            &&& pre.thrd_mp.dom().contains(thread)
            &&& pre.thrd_mp.spec_index(thread).view().owning_container == container
            &&& old_page.owning_container == container
        }),
    ensures page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); };
}

proof fn pop_stage_2m_page_eof_quota(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let old_thread = pre.thrd_mp.spec_index(thread);
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& page_ptr_valid(page)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& pre.ctn_mp.dom().contains(container)
            &&& pre.ctn_mp.spec_index(container).view_rodata().view().allocator_ptr_2m == allocator
            &&& pre.thrd_mp.dom().contains(thread)
            &&& thread_effective_quota_2m(old_thread) >= 1
            &&& old_thread.view().owning_container == container
            &&& pre.allc_2m_mp.dom().contains(allocator)
            &&& pre.allc_2m_mp.spec_index(allocator).total_free_pages.view() > 0
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
            &&& old_page.free_list_node_storage.addr() == node
            &&& old_page.owning_container == container
            &&& !old_thread.view().temp_alloc_cache_2m.view().contains(page)
        }),
        post.subsystems_inv(),
    ensures
        container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp),
        container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp),
        container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by {
        reveal(container_process_allocator_quota_2m_wf); reveal(container_thread_wf); reveal(container_allocator_wf);
        lemma_thread_effective_quota_2m_fold_change_by_forall(thread, -1); lemma_thread_effective_quota_2m_fold_sum_eq_forall();
        lemma_thread_pending_2m_folds_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
    };
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by {
        reveal(container_process_allocator_quota_4k_wf); reveal(container_thread_wf); lemma_thread_effective_quota_4k_fold_sum_eq_forall();
        lemma_thread_pending_4k_folds_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
    };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by {
        reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf); lemma_thread_effective_quota_1g_fold_sum_eq_forall();
        lemma_thread_pending_1g_folds_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
    };
}

proof fn pop_stage_2m_page_eof_page_types(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
        }),
        post.subsystems_inv(),
    ensures
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr),
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_2m_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_lower_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
}

proof fn pop_stage_2m_page_eof_staged_pages(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let old_thread = pre.thrd_mp.spec_index(thread);
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& page_ptr_valid(page)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& pre.ctn_mp.dom().contains(container)
            &&& pre.ctn_mp.spec_index(container).view_rodata().view().allocator_ptr_2m == allocator
            &&& pre.thrd_mp.dom().contains(thread)
            &&& thread_effective_quota_2m(old_thread) >= 1
            &&& old_thread.view().owning_container == container
            &&& pre.allc_2m_mp.dom().contains(allocator)
            &&& pre.allc_2m_mp.spec_index(allocator).total_free_pages.view() > 0
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
            &&& old_page.free_list_node_storage.addr() == node
            &&& old_page.owning_container == container
            &&& !old_thread.view().temp_alloc_cache_2m.view().contains(page)
        }),
        post.subsystems_inv(),
    ensures
        thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr),
        thread_staged_pages_wf(post.thrd_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(thread_staged_2m_pages_wf); page_ptr_roundtrip(); };
    assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by {
        assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by {
        assert(post.pg_arr.spec_index(page_ptr2page_index(page)).view().view().mappings() == pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view().mappings());
        reveal(process_emptied_tables_wf);
    };
}

proof fn pop_stage_2m_page_eof_global_pool(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        allocator_perms_wf(pre.allc_2m_mp),
        allocator_free_page_ptrs_wf(pre.allc_2m_mp),
        allocator_free_2m_pages_wf(pre.allc_2m_mp, pre.pg_arr),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& page_ptr_valid(page)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& pre.ctn_mp.dom().contains(container)
            &&& pre.ctn_mp.spec_index(container).view_rodata().view().allocator_ptr_2m == allocator
            &&& pre.allc_2m_mp.dom().contains(allocator)
            &&& pre.allc_2m_mp.spec_index(allocator).total_free_pages.view() > 0
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
            &&& old_page.free_list_node_storage.addr() == node
            &&& old_page.owning_container == container
        }),
    ensures allocator_global_pool_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
{
    hide(Seq::contains);
    reveal(pop_stage_2m_page_eof_transition_framing);
    if source is Some {
        assert(allocator_global_pool_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by {
            reveal(allocator_perms_wf); reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf); reveal(allocator_free_page_ptrs_wf);
            page_ptr_valid_imply_page_index_valid();
        };
    } else {
        assert(allocator_global_pool_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by {
            page_ptr2page_index_injective();
            reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf); reveal(allocator_free_page_ptrs_wf); reveal(allocator_perms_wf);
            reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list);
            seq_skip_one_implies_contains_and_index_shift::<PagePtr>();
        };
    }
}

proof fn pop_stage_2m_page_eof_cpu_cache(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        allocator_perms_wf(pre.allc_2m_mp),
        allocator_perms_wf(post.allc_2m_mp),
        allocator_free_page_ptrs_wf(pre.allc_2m_mp),
        allocator_free_2m_pages_wf(pre.allc_2m_mp, pre.pg_arr),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& page_ptr_valid(page)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& pre.ctn_mp.dom().contains(container)
            &&& pre.ctn_mp.spec_index(container).view_rodata().view().allocator_ptr_2m == allocator
            &&& pre.allc_2m_mp.dom().contains(allocator)
            &&& pre.allc_2m_mp.spec_index(allocator).total_free_pages.view() > 0
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
            &&& old_page.free_list_node_storage.addr() == node
            &&& old_page.owning_container == container
        }),
    ensures allocator_cpu_cache_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
{
    hide(Seq::contains);
    reveal(pop_stage_2m_page_eof_transition_framing);
    if source is Some {
        assert(allocator_cpu_cache_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by {
            reveal(allocator_perms_wf); page_ptr_roundtrip();
            reveal(allocator_free_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf); reveal(allocator_free_page_ptrs_wf);
            reveal(LinkedList::value_list_unique); reveal(LinkedList::wf_value_list);
            seq_skip_one_implies_contains_and_index_shift::<PagePtr>();
        };
    } else {
        assert(allocator_cpu_cache_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by {
            reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf); reveal(allocator_free_page_ptrs_wf);
            page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective(); reveal(allocator_perms_wf);
        };
    }
}

proof fn pop_stage_2m_page_eof_free_4k_pages(pre: KernelK, post: KernelK, page: PagePtr)
    requires
        allocator_free_page_ptrs_wf(pre.allc_4k_mp),
        allocator_free_4k_pages_wf(pre.allc_4k_mp, pre.pg_arr),
        index_valid(NUM_PAGES, page_ptr2page_index(page)),
        post.allc_4k_mp == pre.allc_4k_mp,
        post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_ptr2page_index(page)),
        pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view().state is Free2m,
        post.pg_arr.spec_index(page_ptr2page_index(page)).view().view().state is Owned2m,
    ensures
        allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_cpu_cache_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
{
    assert(allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_cpu_cache_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by {
        assert forall|k: PageIndex| index_valid(NUM_PAGES, k) && (post.pg_arr.spec_index(k).view().view().state matches PageState::Free4k { allocator_ptr: _, state: FreePageAllocatorState::PreCpuCache { .. } }) implies ({
            let allocator_ptr_4k = post.pg_arr.spec_index(k).view().view().state->Free4k_allocator_ptr.view();
            let cpu_id = post.pg_arr.spec_index(k).view().view().state->Free4k_state->PreCpuCache_cpu_id;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& post.allc_4k_mp.dom().contains(allocator_ptr_4k)
            &&& post.allc_4k_mp.spec_index(allocator_ptr_4k).owning_container == post.pg_arr.spec_index(k).view().view().owning_container
            &&& post.allc_4k_mp.spec_index(allocator_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(k))
            &&& post.allc_4k_mp.spec_index(allocator_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(post.pg_arr.spec_index(k).view().view().free_list_node_storage.addr())
            &&& post.allc_4k_mp.spec_index(allocator_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(post.pg_arr.spec_index(k).view().view().free_list_node_storage.addr()) == page_index2page_ptr(k)
        }) by { allocator_free_4k_pages_wf_at(pre.allc_4k_mp, pre.pg_arr, k); };
        reveal(allocator_free_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf); reveal(allocator_free_page_ptrs_wf);
    };
}

proof fn pop_stage_2m_page_eof_free_1g_pages(pre: KernelK, post: KernelK, page: PagePtr)
    requires
        allocator_free_page_ptrs_wf(pre.allc_1g_mp),
        allocator_free_1g_pages_wf(pre.allc_1g_mp, pre.pg_arr),
        index_valid(NUM_PAGES, page_ptr2page_index(page)),
        post.allc_1g_mp == pre.allc_1g_mp,
        post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_ptr2page_index(page)),
        pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view().state is Free2m,
        post.pg_arr.spec_index(page_ptr2page_index(page)).view().view().state is Owned2m,
    ensures
        allocator_global_pool_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
        allocator_cpu_cache_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    assert(allocator_global_pool_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(allocator_free_1g_pages_wf); reveal(allocator_global_pool_1g_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_cpu_cache_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(allocator_free_1g_pages_wf); reveal(allocator_cpu_cache_1g_pages_wf); reveal(allocator_free_page_ptrs_wf); page_index_roundtrip(); };
}

proof fn pop_stage_2m_page_eof_free_pages(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& page_ptr_valid(page)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& pre.ctn_mp.dom().contains(container)
            &&& pre.ctn_mp.spec_index(container).view_rodata().view().allocator_ptr_2m == allocator
            &&& pre.allc_2m_mp.dom().contains(allocator)
            &&& pre.allc_2m_mp.spec_index(allocator).total_free_pages.view() > 0
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
            &&& old_page.free_list_node_storage.addr() == node
            &&& old_page.owning_container == container
        }),
        post.subsystems_inv(),
    ensures
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_page_ptrs_wf(post.allc_1g_mp),
        allocator_global_pool_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_cpu_cache_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_cpu_cache_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_global_pool_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
        allocator_cpu_cache_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp) && allocator_free_page_ptrs_wf(post.allc_2m_mp) && allocator_free_page_ptrs_wf(post.allc_1g_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    pop_stage_2m_page_eof_global_pool(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_cpu_cache(pre, post, allocator, thread, container, page, node, source);
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_free_2m_pages_wf); };
    pop_stage_2m_page_eof_free_4k_pages(pre, post, page);
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); };
    pop_stage_2m_page_eof_free_1g_pages(pre, post, page);
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(allocator_free_1g_pages_wf); };
}

proof fn pop_stage_2m_page_eof_memory_management_inv(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let old_thread = pre.thrd_mp.spec_index(thread);
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& page_ptr_valid(page)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& pre.ctn_mp.dom().contains(container)
            &&& pre.ctn_mp.spec_index(container).view_rodata().view().allocator_ptr_2m == allocator
            &&& pre.thrd_mp.dom().contains(thread)
            &&& thread_effective_quota_2m(old_thread) >= 1
            &&& old_thread.view().owning_container == container
            &&& pre.allc_2m_mp.dom().contains(allocator)
            &&& pre.allc_2m_mp.spec_index(allocator).total_free_pages.view() > 0
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
            &&& old_page.free_list_node_storage.addr() == node
            &&& old_page.owning_container == container
            &&& !old_thread.view().temp_alloc_cache_2m.view().contains(page)
        }),
        post.subsystems_inv(),
    ensures post.memory_management_inv(),
{
    pop_stage_2m_page_eof_cpu_set_pages(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_allocator_2m_pages(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_allocator_4k_pages(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_allocator_1g_pages(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_container_page_owner(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_container_process_page_pagetable(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_container_pages(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_process_pages(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_page_object_owner(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_quota(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_page_types(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_staged_pages(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_free_pages(pre, post, allocator, thread, container, page, node, source);
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(pop_stage_2m_page_eof_transition_framing); reveal(container_kill_retire_wf); };
    assert(allocator_1g_cpu_caches_empty_wf(post.allc_1g_mp)) by { reveal(pop_stage_2m_page_eof_transition_framing); };
}

proof fn pop_stage_2m_page_eof_thread_endpoint_ref_counter(pre: KernelK, post: KernelK, thread: RwLockThreadPtr)
    requires
        thread_endpoint_ref_counter_wf(pre.thrd_mp, pre.ep_mp),
        post.ep_mp == pre.ep_mp,
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thread),
        forall|t: RwLockThreadPtr, i: EndpointIdx| #![trigger post.thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(i as int)]
            pre.thrd_mp.dom().contains(t) ==>
                post.thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(i as int) == pre.thrd_mp.spec_index(t).view().endpoint_descriptors.view().spec_index(i as int),
    ensures thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp),
{ reveal(thread_endpoint_ref_counter_wf); }

proof fn pop_stage_2m_page_eof_process_management_inv(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        pre.thrd_mp.dom().contains(thread),
        post.subsystems_inv(),
    ensures post.process_management_inv(),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    pop_stage_2m_page_eof_thread_endpoint_ref_counter(pre, post, thread);
    assert(post.process_management_inv()) by {
        assert(thread_caller_callee_wf(post.thrd_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp); };
        assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
        assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.ep_mp); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.sched_mp); };
        assert(container_thread_wf(post.ctn_mp, post.thrd_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp); };
        assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thrd_mp, post.thrd_mp); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.cpu_arr); };
    };
}

pub(super) proof fn pop_stage_2m_page_eof(pre: KernelK, post: KernelK, allocator: RwLockPageAllocatorPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr, page: PagePtr, node: usize, source: Option<CpuId>)
    requires
        pre.inv(),
        pop_stage_2m_page_eof_transition_framing(pre, post, allocator, thread, container, page, node, source),
        ({
            let old_page = pre.pg_arr.spec_index(page_ptr2page_index(page)).view().view();
            let old_thread = pre.thrd_mp.spec_index(thread);
            let free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
            &&& page_ptr_valid(page)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page))
            &&& pre.ctn_mp.dom().contains(container)
            &&& pre.ctn_mp.spec_index(container).view_rodata().view().allocator_ptr_2m == allocator
            &&& pre.thrd_mp.dom().contains(thread)
            &&& thread_effective_quota_2m(old_thread) >= 1
            &&& old_thread.view().owning_container == container
            &&& pre.allc_2m_mp.dom().contains(allocator)
            &&& pre.allc_2m_mp.spec_index(allocator).total_free_pages.view() > 0
            &&& old_page.state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state: free_state })
            &&& old_page.free_list_node_storage.addr() == node
            &&& old_page.owning_container == container
            &&& !old_thread.view().temp_alloc_cache_2m.view().contains(page)
        }),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_2m_mp.spec_index(allocator).wf(),
    ensures post.inv(),
{
    reveal(pop_stage_2m_page_eof_transition_framing);
    pop_stage_2m_page_eof_subsystems_inv(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_memory_management_inv(pre, post, allocator, thread, container, page, node, source);
    pop_stage_2m_page_eof_process_management_inv(pre, post, allocator, thread, container, page, node, source);
}
}
