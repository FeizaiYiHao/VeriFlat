use vstd::prelude::*;
use crate::*;
use super::*;

verus! {

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_allocator_free_4k_global_ptr_valid(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize, alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr
)
    requires
        pre.inv(),
        forall|ptr: PagePtr|
            #![trigger funding_pages.to_set().contains(ptr)]
            funding_pages.to_set().contains(ptr) ==> page_ptr_valid(ptr),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k
        ),
        post.allc_4k_mp.dom().contains(alloc_ptr),
        post.allc_4k_mp.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k
            ),
            post.allc_4k_mp.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
        ]
        page_ptr_valid(page_ptr),
{
    reveal(publish_staged_container_root_kernel_state_framing);
    if alloc_ptr == allocator_4k_page {
        funding_pages.to_set_ensures();
    } else {
        reveal(allocator_free_page_ptrs_wf);
    }
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_allocator_free_4k_global_backward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize, alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr
)
    requires
        pre.inv(),
        container_allocator_global_free_4k_backward_wf(pre.allc_4k_mp, pre.pg_arr,),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        forall|ptr: PagePtr|
            #![trigger funding_pages.to_set().contains(ptr)]
            funding_pages.to_set().contains(ptr) ==> page_ptr_valid(ptr),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k
        ),
        post.allc_4k_mp.dom().contains(alloc_ptr),
        post.allc_4k_mp.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k
            ),
            post.allc_4k_mp.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
        ]
        {
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free4k {
                    allocator_ptr: Ghost(alloc_ptr),
                    state: FreePageAllocatorState::GlobalList,
                }
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == post.allc_4k_mp.spec_index(alloc_ptr).owning_container
        },
{
    reveal(publish_staged_container_root_kernel_state_framing);
    eof_allocator_free_4k_global_ptr_valid(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, alloc_ptr, page_ptr
    );
    page_ptr_valid_imply_page_index_valid();
    page_ptr_roundtrip();
    if alloc_ptr == allocator_4k_page {
        funding_pages.to_set_ensures();
    } else {
        eof_unmodified_object_page_state_eq(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_ptr2page_index(page_ptr)
        );
    }
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_allocator_free_1g_global_forward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize, page_index: PageIndex
)
    requires
        container_allocator_global_free_1g_page_wf(pre.allc_1g_mp, pre.pg_arr,),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k
        ),
        index_valid(NUM_PAGES, page_index),
        post.pg_arr.spec_index(page_index).view().view().state
            matches PageState::Free1g {
                allocator_ptr: _,
                state: FreePageAllocatorState::GlobalList,
            },
        post.pg_arr.spec_index(page_index).view().view().state == pre.pg_arr.spec_index(page_index).view().view().state,
        post.pg_arr.spec_index(page_index).view().view().owning_container == pre.pg_arr.spec_index(page_index).view().view().owning_container,
        post.pg_arr.spec_index(page_index).view().view().free_list_node_storage == pre.pg_arr.spec_index(page_index).view().view().free_list_node_storage,
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k
            ),
            post.pg_arr.spec_index(page_index).view().view().state,
            pre.pg_arr.spec_index(page_index).view().view().state
        ]
        {
            let allocator_ptr_1g = post.pg_arr.spec_index(page_index).view().view().state->Free1g_allocator_ptr.view();
            &&& post.allc_1g_mp.dom().contains(allocator_ptr_1g)
            &&& post.allc_1g_mp.spec_index(allocator_ptr_1g).owning_container == post.pg_arr.spec_index(page_index).view().view().owning_container
            &&& post.allc_1g_mp.spec_index(allocator_ptr_1g).global_pool.view().view().contains(page_index2page_ptr(page_index))
            &&& post.allc_1g_mp.spec_index(allocator_ptr_1g).global_pool.view().map().dom().contains(
                    post.pg_arr.spec_index(page_index).view().view().free_list_node_storage.addr())
            &&& post.allc_1g_mp.spec_index(allocator_ptr_1g).global_pool.view().map().spec_index(
                    post.pg_arr.spec_index(page_index).view().view().free_list_node_storage.addr()) == page_index2page_ptr(page_index)
        },
{
    reveal(publish_staged_container_root_kernel_state_framing);
    let allocator_ptr_1g = post.pg_arr.spec_index(page_index).view().view().state->Free1g_allocator_ptr.view();
    assert(pre.allc_1g_mp.dom().contains(allocator_ptr_1g)) by { reveal(container_allocator_global_free_1g_page_wf); };
    reveal(container_allocator_global_free_1g_page_wf);
}

#[verifier::spinoff_prover]
pub(super) broadcast proof fn eof_allocator_free_1g_global_backward(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize, alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr
)
    requires
        container_allocator_global_free_1g_page_wf(pre.allc_1g_mp, pre.pg_arr,),
        allocator_free_page_ptrs_wf(pre.allc_1g_mp),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k
        ),
        alloc_ptr != allocator_1g_page,
        post.allc_1g_mp.dom().contains(alloc_ptr),
        post.allc_1g_mp.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k
            ),
            post.allc_1g_mp.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
        ]
        {
            &&& page_ptr_valid(page_ptr)
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page_ptr))
            &&& pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Free1g {
                    allocator_ptr: Ghost(alloc_ptr),
                    state: FreePageAllocatorState::GlobalList,
                }
            &&& pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == pre.allc_1g_mp.spec_index(alloc_ptr).owning_container
        },
{
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(page_ptr_valid(page_ptr)) by { reveal(allocator_free_page_ptrs_wf); };
    page_ptr_valid_imply_page_index_valid();
    reveal(container_allocator_global_free_1g_page_wf);
}

#[verifier::spinoff_prover]
pub(super) proof fn eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize
)
    requires
        pre.inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k
        ),
    ensures
        container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp),
        container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp),
        container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp),
{
    reveal(publish_staged_container_root_kernel_state_framing);
    let child_processes = post.ctn_mp.spec_index(container_page).view().owned_processes.view();
    let child_threads = post.ctn_mp.spec_index(container_page).view_ghost().owned_threads.view();
    let child_indirect_threads = post.ctn_mp.spec_index(container_page).view_ghost().owned_indirect_threads.view();
    let child_depth = post.ctn_mp.spec_index(container_page).view_rodata().view().depth as int;
    assert(container_process_wf(pre.ctn_mp, pre.prc_mp) && container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp) && container_thread_wf(post.ctn_mp, pre.thr_mp)) by { reveal(container_thread_wf); };
    lemma_process_effective_quota_folds_singleton(child_processes, post.prc_mp, process_page);
    lemma_thread_quota_folds_empty(child_threads, pre.thr_mp, child_depth);
    lemma_thread_quota_folds_empty(child_indirect_threads, pre.thr_mp, child_depth);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, pre.thr_mp, post.allc_4k_mp)) by {
        reveal(container_process_allocator_quota_4k_wf); reveal(container_process_wf); reveal(container_allocator_wf);
        lemma_process_effective_quota_4k_fold_sum_eq_forall();
    };
    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_4k_mp);
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, pre.thr_mp, post.allc_2m_mp)) by {
        reveal(container_process_allocator_quota_2m_wf); reveal(container_process_wf); reveal(container_allocator_wf);
        lemma_process_effective_quota_2m_fold_sum_eq_forall();
    };
    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_2m_mp);
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, pre.thr_mp, post.allc_1g_mp)) by {
        reveal(container_process_allocator_quota_1g_wf); reveal(container_process_wf); reveal(container_allocator_wf);
        lemma_process_effective_quota_1g_fold_sum_eq_forall();
    };
    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thr_mp, post.thr_mp, post.allc_1g_mp);

}

#[verifier::spinoff_prover]
pub(super) proof fn eof_allocator_free_pages_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        forall|page_ptr: PagePtr|
            #![trigger funding_pages.to_set().contains(page_ptr)]
            funding_pages.to_set().contains(page_ptr) ==> page_ptr_valid(page_ptr),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k
        ),
    ensures
        post.allocator_free_pages_wf(),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(publish_staged_container_root_kernel_state_framing);
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_2m_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_1g_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_global_free_4k_forward_wf(pre.allc_4k_mp, pre.pg_arr,)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); };
    assert(container_allocator_global_free_4k_backward_wf(pre.allc_4k_mp, pre.pg_arr,)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); };
    assert(container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr,)) by {
        assert(container_allocator_global_free_4k_forward_wf(post.allc_4k_mp, post.pg_arr,)) by {
            page_ptr_valid_imply_page_index_valid();
            page_ptr_roundtrip();
            broadcast use eof_unmodified_object_page_state_eq;
        };
        assert(container_allocator_global_free_4k_backward_wf(post.allc_4k_mp, post.pg_arr,)) by { broadcast use eof_allocator_free_4k_global_backward; };
        reveal(container_allocator_global_free_4k_page_wf);
    };
    assert(container_allocator_cpu_cache_free_4k_page_wf(post.allc_4k_mp, post.pg_arr,)) by {
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        broadcast use eof_unmodified_object_page_state_eq;
        reveal(container_allocator_free_4k_page_wf);
        reveal(container_allocator_cpu_cache_free_4k_page_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr,)) by { reveal(container_allocator_free_4k_page_wf); };
    assert(container_allocator_global_free_2m_page_wf(post.allc_2m_mp, post.pg_arr,)) by {
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        broadcast use eof_unmodified_object_page_state_eq;
        reveal(container_allocator_free_2m_page_wf);
        reveal(container_allocator_global_free_2m_page_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_cpu_cache_free_2m_page_wf(post.allc_2m_mp, post.pg_arr,)) by {
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        broadcast use eof_unmodified_object_page_state_eq;
        reveal(container_allocator_free_2m_page_wf);
        reveal(container_allocator_cpu_cache_free_2m_page_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr,)) by { reveal(container_allocator_free_2m_page_wf); };
    assert(container_allocator_global_free_1g_page_wf(post.allc_1g_mp, post.pg_arr,)) by {
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        broadcast use eof_unmodified_object_page_state_eq;
        reveal(container_allocator_free_1g_page_wf);
        reveal(container_allocator_global_free_1g_page_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_cpu_cache_free_1g_page_wf(post.allc_1g_mp, post.pg_arr,)) by {
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        broadcast use eof_unmodified_object_page_state_eq;
        reveal(container_allocator_free_1g_page_wf);
        reveal(container_allocator_cpu_cache_free_1g_page_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr,)) by { reveal(container_allocator_free_1g_page_wf); };
    assert(container_allocator_4k_forward_wf(post.ctn_mp, post.allc_4k_mp)) by { reveal(container_allocator_wf); };
    assert(container_allocator_4k_backward_wf(post.ctn_mp, post.allc_4k_mp)) by { reveal(container_allocator_wf); };
    assert(container_allocator_2m_forward_wf(post.ctn_mp, post.allc_2m_mp)) by { reveal(container_allocator_wf); };
    assert(container_allocator_2m_backward_wf(post.ctn_mp, post.allc_2m_mp)) by { reveal(container_allocator_wf); };
    assert(container_allocator_1g_forward_wf(post.ctn_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_allocator_1g_backward_wf(post.ctn_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp,)) by { reveal(container_allocator_wf); };
}
}
