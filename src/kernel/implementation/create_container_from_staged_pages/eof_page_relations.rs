use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_allocator_pages_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp,),
{
    assert(allocator_pages_wf(pre.pg_arr, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp,)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    assert(allocator_4k_pages_forward_wf(pre.pg_arr, pre.allc_4k_mp)) by { reveal(allocator_4k_pages_wf); };
    assert(allocator_4k_pages_backward_wf(pre.pg_arr, pre.allc_4k_mp)) by { reveal(allocator_4k_pages_wf); };
    assert(allocator_2m_pages_forward_wf(pre.pg_arr, pre.allc_2m_mp)) by { reveal(allocator_2m_pages_wf); };
    assert(allocator_2m_pages_backward_wf(pre.pg_arr, pre.allc_2m_mp)) by { reveal(allocator_2m_pages_wf); };
    assert(allocator_1g_pages_forward_wf(pre.pg_arr, pre.allc_1g_mp)) by { reveal(allocator_1g_pages_wf); };
    assert(allocator_1g_pages_backward_wf(pre.pg_arr, pre.allc_1g_mp)) by { reveal(allocator_1g_pages_wf); };
    assert(allocator_4k_pages_wf(post.pg_arr, post.allc_4k_mp)) by {
        assert(allocator_4k_pages_forward_wf(post.pg_arr, post.allc_4k_mp)) by {
            page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
            broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
            reveal(publish_staged_container_root_kernel_state_framing); reveal(allocator_4k_pages_forward_wf);
            broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
        };
        assert(allocator_4k_pages_backward_wf(post.pg_arr, post.allc_4k_mp)) by {
            page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
            broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
            reveal(publish_staged_container_root_kernel_state_framing); reveal(allocator_4k_pages_backward_wf);
            broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
        };
        reveal(allocator_4k_pages_wf);
    };
    assert(allocator_2m_pages_wf(post.pg_arr, post.allc_2m_mp)) by {
        assert(allocator_2m_pages_forward_wf(post.pg_arr, post.allc_2m_mp)) by {
            page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
            broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
            reveal(publish_staged_container_root_kernel_state_framing); reveal(allocator_2m_pages_forward_wf);
            broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
        };
        assert(allocator_2m_pages_backward_wf(post.pg_arr, post.allc_2m_mp)) by {
            page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
            broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
            reveal(publish_staged_container_root_kernel_state_framing); reveal(allocator_2m_pages_backward_wf);
            broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
        };
        reveal(allocator_2m_pages_wf);
    };
    assert(allocator_1g_pages_wf(post.pg_arr, post.allc_1g_mp)) by {
        assert(allocator_1g_pages_forward_wf(post.pg_arr, post.allc_1g_mp)) by {
            page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
            broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
            reveal(publish_staged_container_root_kernel_state_framing); reveal(allocator_1g_pages_forward_wf);
            broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
        };
        assert(allocator_1g_pages_backward_wf(post.pg_arr, post.allc_1g_mp)) by {
            page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
            broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
            reveal(publish_staged_container_root_kernel_state_framing); reveal(allocator_1g_pages_backward_wf);
            broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
        };
        reveal(allocator_1g_pages_wf);
    };
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub broadcast proof fn publish_staged_container_root_eof_existing_pagetable_closure_page_backward(
    pre: KernelK,
    post: KernelK,
    parent_container_ptr: RwLockContainerPtr,
    current_thread_ptr: RwLockThreadPtr,
    container_page: PagePtr,
    pcid_allocator_page: PagePtr,
    allocator_4k_page: PagePtr,
    allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr,
    scheduler_page: PagePtr,
    cpu_set_page: PagePtr,
    process_page: PagePtr,
    pagetable_page: PagePtr,
    l4_page: PagePtr,
    thread_page: PagePtr,
    funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize,
    process_quota_4k: usize,
    pt_ptr: RwLockPageTableRoot,
    pt_page_ptr: PagePtr,
)
    requires
        pre.inv(),
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        post.pt_mp.dom().contains(pt_ptr),
        post.pt_mp.spec_index(pt_ptr).view().page_closure().contains(pt_page_ptr),
        pt_ptr != pagetable_page,
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pt_mp.spec_index(pt_ptr).view().page_closure().contains(pt_page_ptr)
        ]
        {
            &&& page_ptr_valid(pt_page_ptr)
            &&& post.pg_arr.spec_index(page_ptr2page_index(pt_page_ptr)).view().view().state is Allocated4k
            &&& post.pg_arr.spec_index(page_ptr2page_index(pt_page_ptr)).view().view().state->Allocated4k_state is PageTable
            &&& post.pg_arr.spec_index(page_ptr2page_index(pt_page_ptr)).view().view().state->Allocated4k_state ->PageTable_pagetable_root == pt_ptr
        },
{
    assert(pre.pt_mp.dom().contains(pt_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); broadcast use vstd::set::lemma_set_insert_different; };
    assert(post.pt_mp.spec_index(pt_ptr) == pre.pt_mp.spec_index(pt_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert(pre.pt_mp.spec_index(pt_ptr).view().page_closure().contains(pt_page_ptr));
    assert(pagetable_pages_wf(pre.pt_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    assert(pagetable_closure_page_backward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(page_ptr_valid(pt_page_ptr)) by { reveal(pagetable_closure_page_backward_wf); };
    assert(pre.pg_arr.spec_index(page_ptr2page_index(pt_page_ptr)).view().view().state matches PageState::Allocated4k {
            state: Allocated4KPageState::PageTable { pagetable_root },
        }) by { reveal(pagetable_closure_page_backward_wf); };
    assert(page_ptr2page_index(pt_page_ptr) != page_ptr2page_index(l4_page)) by {
        if page_ptr2page_index(pt_page_ptr) == page_ptr2page_index(l4_page) {
            assert(pt_page_ptr == l4_page) by { page_ptr2page_index_injective(); };
            assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(l4_page)) by {
                reveal(new_container_bootstrap_4k_pages); reveal(publish_staged_container_root_kernel_state_framing);
                broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
            };
            assert(thread_staged_pages_4k_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
            reveal(thread_staged_pages_4k_wf);
        }
    };
    page_ptr_valid_imply_page_index_valid();
    publish_staged_container_root_eof_unmodified_object_page_state_eq(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_ptr2page_index(pt_page_ptr),
    );
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_pagetable_pages_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        pagetable_pages_wf(post.pt_mp, post.pg_arr),
{
    assert(pagetable_pages_wf(pre.pt_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    assert(pagetable_root_page_forward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(pagetable_closure_page_forward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(pagetable_root_page_backward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(pagetable_closure_page_backward_wf(pre.pt_mp, pre.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(pagetable_root_page_forward_wf(post.pt_mp, post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
        reveal(publish_staged_container_root_kernel_state_framing); reveal(pagetable_root_page_forward_wf);
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(pagetable_closure_page_forward_wf(post.pt_mp, post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
        reveal(publish_staged_container_root_kernel_state_framing); reveal(pagetable_closure_page_forward_wf);
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(pagetable_root_page_backward_wf(post.pt_mp, post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
        reveal(publish_staged_container_root_kernel_state_framing); reveal(pagetable_root_page_backward_wf);
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(pagetable_closure_page_backward_wf(post.pt_mp, post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_existing_pagetable_closure_page_backward;
        reveal(publish_staged_container_root_kernel_state_framing); reveal(pagetable_closure_page_backward_wf);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_page_pagetable_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
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
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        page_pagetable_wf(post.pt_mp, post.pg_arr),
{
    assert(page_pagetable_wf(pre.pt_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    assert(mapped_4k_page_pagetable_wf(pre.pt_mp, pre.pg_arr));
    assert(mapped_2m_page_pagetable_wf(pre.pt_mp, pre.pg_arr));
    assert(mapped_1g_page_pagetable_wf(pre.pt_mp, pre.pg_arr));
    assert(pagetable_perms_wf(post.pt_mp)) by { reveal(KernelK::subsystems_inv); };
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(mapped_4k_page_pagetable_wf);
        reveal(pagetable_perms_wf);
        reveal(PageTable::is_empty);
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(mapped_2m_page_pagetable_wf);
        reveal(pagetable_perms_wf);
        reveal(PageTable::is_empty);
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(mapped_1g_page_pagetable_wf);
        reveal(pagetable_perms_wf);
        reveal(PageTable::is_empty);
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
}


}
