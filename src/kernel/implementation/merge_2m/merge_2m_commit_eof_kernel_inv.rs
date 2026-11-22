#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scan::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_commit_spec::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_commit_eof_allocator::*;

#[cfg(verus_keep_ghost)]
use super::merge_2m_commit_eof::{merge_2m_commit_eof_implies_container_owned_pages_wf, merge_2m_commit_eof_implies_hugepage_2m_wf,
    merge_2m_commit_eof_implies_mapped_4k_page_pagetable_wf, merge_2m_commit_eof_implies_mapped_2m_page_pagetable_wf,
    merge_2m_commit_eof_implies_typed_lock_maps_aligned};

verus! {
pub proof fn merge_2m_commit_eof_implies_object_page_invariants(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, candidate: Merge2mCandidate)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_4k >= 512,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        candidate.wf(),
        candidate.sources.len() == 512,
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, candidate),
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
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_pages_wf); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { reveal(process_pages_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); reveal(page_array_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); reveal(page_array_wf); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { reveal(pcid_allocator_pages_wf); };
    assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(thread_staged_4k_pages_wf); };
    assert(thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(thread_staged_2m_pages_wf); };
    assert(thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(thread_staged_1g_pages_wf); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { reveal(process_object_pages_owner_wf); };
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); };
}

pub proof fn merge_2m_commit_eof_implies_kernel_inv(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, candidate: Merge2mCandidate, lctx: &LocalContext)
    requires
        pre.inv(),
        typed_lock_maps_aligned(&pre, lctx),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_4k >= 512,
        pre.thrd_mp.spec_index(thread).view().quota_2m < usize::MAX,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        candidate.wf(),
        candidate.sources.len() == 512,
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, candidate),
        !pre.allc_2m_mp.spec_index(allocator_2m).global_pool.view().map().dom().contains(pre.pg_arr.spec_index(candidate.head).view().view().free_list_node_storage.addr()),
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
    merge_2m_commit_eof_implies_allocator_and_quota_wf(pre, post, thread, allocator_4k, allocator_2m, candidate);
    assert(thread_perms_wf(post.thrd_mp)) by {
        reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked);
        reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
        reveal(thread_exited_only_when_wlocked); reveal(thread_ipc_transit_wf);
    };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    merge_2m_commit_eof_implies_container_owned_pages_wf(pre, post, thread, allocator_4k, allocator_2m, candidate);
    merge_2m_commit_eof_implies_hugepage_2m_wf(pre, post, thread, allocator_4k, allocator_2m, candidate);
    assert(hugepage_1g_wf(post.pg_arr)) by { reveal(hugepage_1g_wf); };
    merge_2m_commit_eof_implies_mapped_4k_page_pagetable_wf(pre, post, thread, allocator_4k, allocator_2m, candidate);
    merge_2m_commit_eof_implies_mapped_2m_page_pagetable_wf(pre, post, thread, allocator_4k, allocator_2m, candidate);
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
    merge_2m_commit_eof_implies_object_page_invariants(pre, post, thread, allocator_4k, allocator_2m, candidate);
    assert(pci_bar_pages_unavailable_wf(post.pci_bars.view(), post.pg_arr)) by { reveal(merge_2m_commit_eof_transition_framing); reveal(pci_bar_pages_unavailable_wf); };
    assert(post.process_management_inv()) by {
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
    merge_2m_commit_eof_implies_typed_lock_maps_aligned(pre, post, thread, allocator_4k, allocator_2m, candidate, lctx);
}
}
