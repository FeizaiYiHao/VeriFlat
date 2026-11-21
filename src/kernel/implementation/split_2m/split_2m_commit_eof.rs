#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::split_2m_commit_spec::*;
#[cfg(verus_keep_ghost)]
use super::split_2m_commit_eof_allocator::*;

verus! {
pub proof fn split_2m_exchange_thread_quotas_eof_implies_thread_inv(pre: Thread, post: Thread)
    requires
        pre.inv(),
        pre.temp_alloc_clean(),
        pre.quota_2m > 0,
        split_2m_exchange_thread_quotas_eof_transition_framing(pre, post),
    ensures
        post.inv(),
{}

pub proof fn split_2m_commit_eof_implies_container_owned_pages_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        container_owned_pages_wf(post.ctn_mp, post.pg_arr),
{
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing);
        reveal(container_owned_pages_wf);
        container_owned_pages_wf_backward_at(pre.ctn_mp, pre.pg_arr, head);
        page_ptr_roundtrip(); page_index_roundtrip();
    };
}

pub proof fn split_2m_commit_eof_implies_mapped_4k_page_pagetable_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        reveal(split_2m_commit_eof_transition_framing); reveal(mapped_4k_page_pagetable_wf);
        reveal(pagetable_lower_wf); page_index_roundtrip();
        page_ptr_valid_imply_page_index_valid();
    };
}

pub proof fn split_2m_commit_eof_implies_mapped_2m_page_pagetable_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        reveal(split_2m_commit_eof_transition_framing); reveal(mapped_2m_page_pagetable_wf);
        reveal(pagetable_lower_wf); page_index_roundtrip();
        page_ptr_valid_imply_page_index_valid();
    };
}

pub proof fn split_2m_commit_eof_implies_typed_lock_maps_aligned(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize, lctx: &LocalContext)
    requires
        pre.inv(),
        typed_lock_maps_aligned(&pre, lctx),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        typed_lock_maps_aligned(&post, lctx),
{
    assert(typed_lock_maps_aligned(&post, lctx)) by {
        reveal(split_2m_commit_eof_transition_framing); reveal(LockedArray::typed_lock_map_aligned);
        reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned);
        reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
    };
}

pub proof fn split_2m_commit_eof_implies_process_management_inv(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        post.process_management_inv(),
{
    assert(post.process_management_inv()) by { reveal(split_2m_commit_eof_transition_framing);
        thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp);
        thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp);
        thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp);
        thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp);
        container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.sched_mp);
        container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
        process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thrd_mp, post.thrd_mp);
        thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.cpu_arr);
        container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.ep_mp);
        assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
    };
}

pub proof fn split_2m_commit_eof_implies_page_object_owner_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
{
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(page_object_owner_wf); reveal(page_array_wf); reveal(hugepage_2m_wf); };
}

pub proof fn split_2m_commit_eof_implies_object_page_invariants(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        container_pages_wf(post.ctn_mp, post.pg_arr),
        process_pages_wf(post.prc_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr),
        thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr),
        thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr),
        thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
        page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
{
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(container_pages_wf); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(process_pages_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(pagetable_pages_wf); reveal(page_array_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(iommu_table_pages_wf); reveal(page_array_wf); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(thread_pages_wf); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(scheduler_pages_wf); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(pcid_allocator_pages_wf); };
    assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(thread_staged_4k_pages_wf); };
    assert(thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(thread_staged_2m_pages_wf); };
    assert(thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(thread_staged_1g_pages_wf); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(endpoint_pages_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(process_emptied_tables_wf); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); reveal(process_object_pages_owner_wf); };
    split_2m_commit_eof_implies_page_object_owner_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
}

pub proof fn split_2m_eof_page_state_transition_implies_hugepage_2m_wf(pre: PageLockedArray, post: PageLockedArray, head: PageIndex)
    requires
        hugepage_2m_wf(pre),
        page_index_2m_valid(head),
        pre.spec_index(head).view().view().state is Free2m,
        forall|index: PageIndex| #![trigger post.spec_index(index)] #![trigger pre.spec_index(index)]
            index_valid(NUM_PAGES, index) && !(head <= index < head + 512) ==> post.spec_index(index).view().view().state == pre.spec_index(index).view().view().state,
        forall|index: PageIndex| #![trigger post.spec_index(index)] head <= index < head + 512 ==> post.spec_index(index).view().view().state is Free4k,
    ensures
        hugepage_2m_wf(post),
{
    assert(hugepage_2m_wf(post)) by {
        reveal(hugepage_2m_wf);
        split_2m_eof_page_state_transition_implies_hugepage_2m_head_aligned_wf(pre, post, head);
        split_2m_eof_page_state_transition_implies_hugepage_2m_tail_forward_wf(pre, post, head);
        split_2m_eof_page_state_transition_implies_hugepage_2m_tail_backward_wf(pre, post, head);
    };
}

pub proof fn split_2m_eof_page_state_transition_implies_hugepage_2m_head_aligned_wf(pre: PageLockedArray, post: PageLockedArray, head: PageIndex)
    requires
        hugepage_2m_wf(pre),
        page_index_2m_valid(head),
        pre.spec_index(head).view().view().state is Free2m,
        forall|index: PageIndex| #![trigger post.spec_index(index)] #![trigger pre.spec_index(index)]
            index_valid(NUM_PAGES, index) && !(head <= index < head + 512) ==> post.spec_index(index).view().view().state == pre.spec_index(index).view().view().state,
        forall|index: PageIndex| #![trigger post.spec_index(index)] head <= index < head + 512 ==> post.spec_index(index).view().view().state is Free4k,
    ensures
        hugepage_2m_head_aligned_wf(post),
{ reveal(hugepage_2m_wf); }

pub proof fn split_2m_eof_page_state_transition_implies_hugepage_2m_tail_forward_wf(pre: PageLockedArray, post: PageLockedArray, head: PageIndex)
    requires
        hugepage_2m_wf(pre),
        page_index_2m_valid(head),
        pre.spec_index(head).view().view().state is Free2m,
        forall|index: PageIndex| #![trigger post.spec_index(index)] #![trigger pre.spec_index(index)]
            index_valid(NUM_PAGES, index) && !(head <= index < head + 512) ==> post.spec_index(index).view().view().state == pre.spec_index(index).view().view().state,
        forall|index: PageIndex| #![trigger post.spec_index(index)] head <= index < head + 512 ==> post.spec_index(index).view().view().state is Free4k,
    ensures
        hugepage_2m_tail_forward_wf(post),
{ reveal(hugepage_2m_wf); }

pub proof fn split_2m_eof_page_state_transition_implies_hugepage_2m_tail_backward_wf(pre: PageLockedArray, post: PageLockedArray, head: PageIndex)
    requires
        hugepage_2m_wf(pre),
        page_index_2m_valid(head),
        pre.spec_index(head).view().view().state is Free2m,
        forall|index: PageIndex| #![trigger post.spec_index(index)] #![trigger pre.spec_index(index)]
            index_valid(NUM_PAGES, index) && !(head <= index < head + 512) ==> post.spec_index(index).view().view().state == pre.spec_index(index).view().view().state,
        forall|index: PageIndex| #![trigger post.spec_index(index)] head <= index < head + 512 ==> post.spec_index(index).view().view().state is Free4k,
    ensures
        hugepage_2m_tail_backward_wf(post),
{ reveal(hugepage_2m_wf); }

pub proof fn split_2m_commit_eof_implies_hugepage_2m_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        hugepage_2m_wf(post.pg_arr),
{
    assert(hugepage_2m_wf(post.pg_arr)) by {
        reveal(split_2m_commit_eof_transition_framing);
        split_2m_eof_page_state_transition_implies_hugepage_2m_wf(pre.pg_arr, post.pg_arr, head);
    };
}

pub proof fn split_2m_commit_eof_implies_hugepage_1g_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        hugepage_1g_wf(post.pg_arr),
{
    assert(hugepage_1g_wf(post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_1g_wf); reveal(hugepage_2m_wf); };
}

pub proof fn split_2m_commit_eof_implies_kernel_inv(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize, lctx: &LocalContext)
    requires
        pre.inv(),
        typed_lock_maps_aligned(&pre, lctx),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.thrd_mp.spec_index(thread).view().quota_4k <= usize::MAX - 512,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.thrd_mp.perms_wf(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        post.inv(),
        typed_lock_maps_aligned(&post, lctx),
{
    split_2m_commit_eof_implies_allocator_and_quota_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    assert(thread_perms_wf(post.thrd_mp)) by { reveal(split_2m_commit_eof_transition_framing);
        reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked);
        reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
    };
    assert(post.subsystems_inv()) by { reveal(split_2m_commit_eof_transition_framing); reveal(KernelK::default_pagetable_wf); };
    split_2m_commit_eof_implies_container_owned_pages_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_hugepage_2m_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_hugepage_1g_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_mapped_4k_page_pagetable_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_mapped_2m_page_pagetable_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
    split_2m_commit_eof_implies_object_page_invariants(pre, post, thread, allocator_4k, allocator_2m, head, source);
    assert(pci_bar_pages_unavailable_wf(post.pci_bars.view(), post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(pci_bar_pages_unavailable_wf); };
    split_2m_commit_eof_implies_process_management_inv(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_typed_lock_maps_aligned(pre, post, thread, allocator_4k, allocator_2m, head, source, lctx);
    assert(post.inv()) by { reveal(split_2m_commit_eof_transition_framing); };
}
}
