use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn create_process_from_staged_pages_eof_memory_management_inv(
    pre: KernelK,
    post: KernelK,
    process_page_ptr: PagePtr,
    pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr,
    parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 3,
        pre.thr_mp.spec_index(staging_thread_ptr)
            .view().temp_alloc_cache_4k.view()
            =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr))
            .view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr))
            .view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr))
            .view().view().owning_container == container_ptr,
        create_process_from_staged_pages_kernel_state_framing(
            pre,
            post,
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
            parent_ptr,
            staging_thread_ptr,
            container_ptr,
            pcid_allocator_ptr,
            pcid,
        ),
    ensures
        post.memory_management_inv(),
{
    create_process_from_staged_pages_eof_page_table_relations(
        pre,
        post,
        process_page_ptr,
        pagetable_page_ptr,
        l4_page_ptr,
        parent_ptr,
        staging_thread_ptr,
        container_ptr,
        pcid_allocator_ptr,
        pcid,
    );
    create_process_from_staged_pages_eof_memory_relations(
        pre,
        post,
        process_page_ptr,
        pagetable_page_ptr,
        l4_page_ptr,
        parent_ptr,
        staging_thread_ptr,
        container_ptr,
        pcid_allocator_ptr,
        pcid,
    );
    create_process_from_staged_pages_eof_allocator_quota_4k_wf(
        pre,
        post,
        process_page_ptr,
        pagetable_page_ptr,
        l4_page_ptr,
        parent_ptr,
        staging_thread_ptr,
        container_ptr,
        pcid_allocator_ptr,
        pcid,
    );
    create_process_from_staged_pages_eof_allocator_quota_2m_wf(
        pre,
        post,
        process_page_ptr,
        pagetable_page_ptr,
        l4_page_ptr,
        parent_ptr,
        staging_thread_ptr,
        container_ptr,
        pcid_allocator_ptr,
        pcid,
    );
    create_process_from_staged_pages_eof_allocator_quota_1g_wf(
        pre,
        post,
        process_page_ptr,
        pagetable_page_ptr,
        l4_page_ptr,
        parent_ptr,
        staging_thread_ptr,
        container_ptr,
        pcid_allocator_ptr,
        pcid,
    );
    assert(container_process_allocator_quota_wf(
        post.ctn_mp,
        post.prc_mp,
        post.thr_mp,
        post.allc_4k_mp,
        post.allc_2m_mp,
        post.allc_1g_mp,
    )) by {
        reveal(container_process_allocator_quota_wf);
    };
    assert(post.memory_management_inv()) by {
        reveal(KernelK::memory_management_inv);
    };
}


}
