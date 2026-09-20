use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_container_page_owner_forward(
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
    c_ptr: RwLockContainerPtr,
    page_ptr: PagePtr,
)
    requires
        container_page_owner_forward_wf(pre.ctn_mp, pre.pg_arr),
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
        post.ctn_mp.dom().contains(c_ptr),
        post.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(page_ptr),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(page_ptr)
        ]
        {
            &&& page_ptr_valid(page_ptr)
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == c_ptr
        },
{
    let moved_pages = new_container_moved_pages(
        container_page,
        pcid_allocator_page,
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        scheduler_page,
        cpu_set_page,
        process_page,
        pagetable_page,
        l4_page,
    ).union(funding_pages.to_set());
    if c_ptr == container_page {
        assert(moved_pages.contains(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
        assert(page_ptr_valid(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
        assert(post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == c_ptr) by {
            if funding_pages.to_set().contains(page_ptr) {
                reveal(publish_staged_container_root_kernel_state_framing);
            } else {
                let container_head = page_ptr2page_index(container_page);
                let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
                assert(new_container_moved_pages(
                    container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page,
                    cpu_set_page, process_page, pagetable_page, l4_page,
                ).contains(page_ptr)) by { broadcast use vstd::set::lemma_set_union; };
                reveal(new_container_moved_pages);
                if page_2m_all_ptrs(container_head).contains(page_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
                    reveal(page_2m_all_ptrs);
                    page_2m_ptr_prefix_member_bounds(container_head, 512, page_ptr);
                    if page_ptr2page_index(page_ptr) != container_head {
                        assert(page_2m_tail_indices(container_head).contains(page_ptr2page_index(page_ptr))) by { reveal(page_2m_tail_indices); reveal(spec_page_index_merge_2m_valid); };
                    }
                    reveal(publish_staged_container_root_kernel_state_framing);
                } else if page_2m_all_ptrs(pcid_allocator_head).contains(page_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
                    reveal(page_2m_all_ptrs);
                    page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, page_ptr,);
                    if page_ptr2page_index(page_ptr) != pcid_allocator_head {
                        assert(page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(page_ptr))) by { reveal(page_2m_tail_indices); reveal(spec_page_index_merge_2m_valid); };
                    }
                    reveal(publish_staged_container_root_kernel_state_framing);
                } else {
                    assert(new_container_bootstrap_4k_pages(
                        allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page,
                        l4_page,
                    ).contains(page_ptr)) by { broadcast use vstd::set::lemma_set_union; };
                    reveal(new_container_bootstrap_4k_pages);
                    reveal(publish_staged_container_root_kernel_state_framing);
                }
            }
        };
    } else if c_ptr == parent_container_ptr {
        assert(pre.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
        assert(!moved_pages.contains(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
        assert(page_ptr_valid(page_ptr)) by { reveal(container_page_owner_forward_wf); };
        assert(pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == parent_container_ptr) by { reveal(container_page_owner_forward_wf); };
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        assert({
            &&& !funding_pages.to_set().contains(page_ptr)
            &&& !new_container_moved_pages(
                container_page,
                pcid_allocator_page,
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(page_ptr)
        }) by { broadcast use vstd::set::lemma_set_union; };
        publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_ptr2page_index(page_ptr),
        );
        assert(post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == c_ptr) by {
        };
    } else {
        assert(pre.ctn_mp.dom().contains(c_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); broadcast use vstd::set::lemma_set_insert_different; };
        assert(post.ctn_mp.spec_index(c_ptr).view() == pre.ctn_mp.spec_index(c_ptr).view()) by { reveal(publish_staged_container_root_kernel_state_framing); };
        assert(pre.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(page_ptr));
        assert(page_ptr_valid(page_ptr)) by { reveal(container_page_owner_forward_wf); };
        assert(pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == c_ptr) by { reveal(container_page_owner_forward_wf); };
        assert(!moved_pages.contains(page_ptr)) by {
            if moved_pages.contains(page_ptr) {
                assert(pre.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
                assert(pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == parent_container_ptr) by { reveal(container_page_owner_forward_wf); };
            }
        };
        page_ptr_valid_imply_page_index_valid();
        page_ptr_roundtrip();
        assert({
            &&& !funding_pages.to_set().contains(page_ptr)
            &&& !new_container_moved_pages(
                container_page,
                pcid_allocator_page,
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(page_ptr)
        }) by { broadcast use vstd::set::lemma_set_union; };
        publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_ptr2page_index(page_ptr),
        );
        assert(post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == c_ptr) by {
        };
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_page_owner_forward_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        container_page_owner_forward_wf(pre.ctn_mp, pre.pg_arr),
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
        container_page_owner_forward_wf(post.ctn_mp, post.pg_arr),
{
    broadcast use publish_staged_container_root_eof_container_page_owner_forward;
    reveal(container_page_owner_forward_wf);
}

#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_container_page_owner_backward(
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
    page_index: PageIndex,
)
    requires
        container_page_owner_backward_wf(pre.ctn_mp, pre.pg_arr),
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
        index_valid(NUM_PAGES, page_index),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(page_index).view().view().owning_container
        ]
        {
            let c_ptr = post.pg_arr.spec_index(page_index).view().view().owning_container;
            &&& post.ctn_mp.dom().contains(c_ptr)
            &&& post.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(page_index2page_ptr(page_index))
        },
{
    let page_ptr = page_index2page_ptr(page_index);
    let moved_pages = new_container_moved_pages(
        container_page,
        pcid_allocator_page,
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        scheduler_page,
        cpu_set_page,
        process_page,
        pagetable_page,
        l4_page,
    ).union(funding_pages.to_set());
    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    if moved_pages.contains(page_ptr) {
        assert(post.pg_arr.spec_index(page_index).view().view().owning_container == container_page) by {
            if funding_pages.to_set().contains(page_ptr) {
                reveal(publish_staged_container_root_kernel_state_framing);
            } else {
                let container_head = page_ptr2page_index(container_page);
                let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
                assert(new_container_moved_pages(
                    container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page,
                    cpu_set_page, process_page, pagetable_page, l4_page,
                ).contains(page_ptr)) by { broadcast use vstd::set::lemma_set_union; };
                reveal(new_container_moved_pages);
                if page_2m_all_ptrs(container_head).contains(page_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
                    reveal(page_2m_all_ptrs);
                    page_2m_ptr_prefix_member_bounds(container_head, 512, page_ptr);
                    if page_index != container_head {
                        assert(page_2m_tail_indices(container_head).contains(page_index)) by { reveal(page_2m_tail_indices); reveal(spec_page_index_merge_2m_valid); };
                    }
                    reveal(publish_staged_container_root_kernel_state_framing);
                } else if page_2m_all_ptrs(pcid_allocator_head).contains(page_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
                    reveal(page_2m_all_ptrs);
                    page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, page_ptr,);
                    if page_index != pcid_allocator_head {
                        assert(page_2m_tail_indices(pcid_allocator_head).contains(page_index)) by { reveal(page_2m_tail_indices); reveal(spec_page_index_merge_2m_valid); };
                    }
                    reveal(publish_staged_container_root_kernel_state_framing);
                } else {
                    assert(new_container_bootstrap_4k_pages(
                        allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page,
                        l4_page,
                    ).contains(page_ptr)) by { broadcast use vstd::set::lemma_set_union; };
                    reveal(new_container_bootstrap_4k_pages);
                    reveal(publish_staged_container_root_kernel_state_framing);
                }
            }
        };
        assert(post.ctn_mp.dom().contains(container_page)) by { reveal(publish_staged_container_root_kernel_state_framing); broadcast use vstd::set::lemma_set_insert_same; };
        assert(post.ctn_mp.spec_index(container_page).view().owned_pages.view().contains(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
    } else {
        assert({
            &&& !funding_pages.to_set().contains(page_ptr)
            &&& !new_container_moved_pages(
                container_page,
                pcid_allocator_page,
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(page_ptr)
        }) by { broadcast use vstd::set::lemma_set_union; };
        publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_index,
        );
        assert(post.pg_arr.spec_index(page_index).view().view().owning_container == pre.pg_arr.spec_index(page_index).view().view().owning_container) by {
        };
        let c_ptr = pre.pg_arr.spec_index(page_index).view().view().owning_container;
        assert(pre.ctn_mp.dom().contains(c_ptr)) by { reveal(container_page_owner_backward_wf); };
        assert(pre.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(page_ptr)) by { reveal(container_page_owner_backward_wf); };
        assert(post.ctn_mp.dom().contains(c_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
        if c_ptr == parent_container_ptr {
            assert(post.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); };
        } else {
            assert(c_ptr != container_page) by { reveal(publish_staged_container_root_kernel_state_framing); };
            assert(post.ctn_mp.spec_index(c_ptr).view() == pre.ctn_mp.spec_index(c_ptr).view()) by { reveal(publish_staged_container_root_kernel_state_framing); };
        }
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_page_owner_backward_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        container_page_owner_backward_wf(pre.ctn_mp, pre.pg_arr),
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
        container_page_owner_backward_wf(post.ctn_mp, post.pg_arr),
{
    broadcast use publish_staged_container_root_eof_container_page_owner_backward;
    reveal(container_page_owner_backward_wf);
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_page_owner_wf(
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
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
{
    assert(container_page_owner_wf(pre.ctn_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    assert(container_page_owner_forward_wf(pre.ctn_mp, pre.pg_arr)) by { reveal(container_page_owner_wf); };
    assert(container_page_owner_backward_wf(pre.ctn_mp, pre.pg_arr)) by { reveal(container_page_owner_wf); };
    publish_staged_container_root_eof_container_page_owner_forward_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_page_owner_backward_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_page_owner_wf); };
}


}
