use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(parent_container_ptr),
        !pre.ctn_mp.dom().contains(container_page),
        pre.ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        pre.thr_mp.dom().contains(current_thread_ptr),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).len() == 8,
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(thread_page),
        funding_pages.no_duplicates(),
        !funding_pages.to_set().contains(thread_page),
        funding_pages.to_set().disjoint(new_container_moved_pages(
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
        )),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        forall|page_ptr: PagePtr|
            #![trigger funding_pages.to_set().contains(page_ptr)]
            funding_pages.to_set().contains(page_ptr) ==> page_ptr_valid(page_ptr),
        pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        page_array_wf(post.pg_arr),
        post.pt_mp.perms_wf(),
        post.pt_mp.dom().contains(pagetable_page),
        post.pt_mp.spec_index(pagetable_page).inv(),
        post.ctn_mp.perms_wf(),
        post.ctn_mp.dom().contains(parent_container_ptr),
        post.ctn_mp.dom().contains(container_page),
        post.ctn_mp.spec_index(parent_container_ptr).inv(),
        post.ctn_mp.spec_index(container_page).inv(),
        post.prc_mp.perms_wf(),
        post.prc_mp.dom().contains(process_page),
        post.prc_mp.spec_index(process_page).inv(),
        post.thr_mp.perms_wf(),
        post.thr_mp.dom().contains(current_thread_ptr),
        post.thr_mp.spec_index(current_thread_ptr).inv(),
        post.sched_mp.perms_wf(),
        post.sched_mp.dom().contains(scheduler_page),
        post.sched_mp.spec_index(scheduler_page).inv(),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.dom().contains(cpu_set_page),
        post.cpu_set_mp.spec_index(cpu_set_page).inv(),
        post.pcid_allc_mp.perms_wf(),
        post.pcid_allc_mp.dom().contains(pcid_allocator_page),
        post.pcid_allc_mp.spec_index(pcid_allocator_page).inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.dom().contains(allocator_4k_page),
        post.allc_4k_mp.spec_index(allocator_4k_page).inv(),
        post.allc_2m_mp.perms_wf(),
        post.allc_2m_mp.dom().contains(allocator_2m_page),
        post.allc_2m_mp.spec_index(allocator_2m_page).inv(),
        post.allc_1g_mp.perms_wf(),
        post.allc_1g_mp.dom().contains(allocator_1g_page),
        post.allc_1g_mp.spec_index(allocator_1g_page).inv(),
    ensures
        post.inv(),
{
    publish_staged_container_root_eof_subsystems_inv(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_memory_relations(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_process_management_inv(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_direct_invariants(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(post.inv()) by { reveal(KernelK::inv); };
}

#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_2m_forward_wf(
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
        pre.inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, page_index),
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
        pre.thr_mp.dom().contains(current_thread_ptr),
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        post.pg_arr.spec_index(page_index).view().view().state is Owned2m,
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(page_index).view().view().state
        ]
        {
            &&& post.thr_mp.dom().contains(
                post.pg_arr.spec_index(page_index).view().view().state->Owned2m_thread_ptr,
            )
            &&& post.thr_mp.spec_index(
                post.pg_arr.spec_index(page_index).view().view().state->Owned2m_thread_ptr,
            ).view().temp_alloc_cache_2m.view().contains(page_index2page_ptr(page_index))
        },
{
    page_index_valid_imply_page_ptr_valid();
    page_index_roundtrip();
    assert(!funding_pages.to_set().contains(page_index2page_ptr(page_index))) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert({
        &&& page_index != page_ptr2page_index(container_page)
        &&& page_index != page_ptr2page_index(pcid_allocator_page)
        &&& !page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_index)
        &&& !page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_index)
        &&& page_index != page_ptr2page_index(allocator_4k_page)
        &&& page_index != page_ptr2page_index(allocator_2m_page)
        &&& page_index != page_ptr2page_index(allocator_1g_page)
        &&& page_index != page_ptr2page_index(scheduler_page)
        &&& page_index != page_ptr2page_index(cpu_set_page)
        &&& page_index != page_ptr2page_index(process_page)
        &&& page_index != page_ptr2page_index(pagetable_page)
        &&& page_index != page_ptr2page_index(l4_page)
    }) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(page_index2page_ptr(page_index))) by {
        reveal(new_container_moved_pages); reveal(new_container_bootstrap_4k_pages); reveal(page_2m_all_ptrs); reveal(page_2m_tail_indices);
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page); page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        broadcast use page_2m_ptr_prefix_member_bounds; broadcast use vstd::set::lemma_set_union;
    };
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_index,
    );
    assert(thread_staged_pages_2m_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    assert(thread_staged_pages_2m_forward_wf(pre.thr_mp, pre.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
    let thread_ptr =
        post.pg_arr.spec_index(page_index).view().view().state->Owned2m_thread_ptr;
    assert(pre.thr_mp.dom().contains(thread_ptr)) by { reveal(thread_staged_pages_2m_forward_wf); };
    assert(pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(page_index2page_ptr(page_index))) by { reveal(thread_staged_pages_2m_forward_wf); };
    assert(thread_ptr != current_thread_ptr);
    assert(post.thr_mp.dom().contains(thread_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(LockedMap::unchanged_except); };
    assert(post.thr_mp.spec_index(thread_ptr) == pre.thr_mp.spec_index(thread_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(LockedMap::unchanged_except); };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_thread_staged_pages_2m_backward_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        pre.thr_mp.dom().contains(current_thread_ptr),
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
        forall|staged_page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(staged_page_ptr)]
            #![trigger funding_pages.to_set().contains(staged_page_ptr)]
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(staged_page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(staged_page_ptr) <==> new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    scheduler_page,
                    cpu_set_page,
                    process_page,
                    pagetable_page,
                    l4_page,
                ).contains(staged_page_ptr) || funding_pages.to_set().contains(staged_page_ptr) || staged_page_ptr == thread_page,
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        thread_staged_pages_2m_backward_wf(post.thr_mp, post.pg_arr),
{
    broadcast use publish_staged_container_root_eof_thread_staged_pages_2m_backward_at;
    reveal(thread_staged_pages_2m_backward_wf);
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_thread_staged_pages_2m_wf(
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
        pre.thr_mp.dom().contains(current_thread_ptr),
        forall|staged_page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(staged_page_ptr)]
            #![trigger funding_pages.to_set().contains(staged_page_ptr)]
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(staged_page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(staged_page_ptr) <==> new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    scheduler_page,
                    cpu_set_page,
                    process_page,
                    pagetable_page,
                    l4_page,
                ).contains(staged_page_ptr) || funding_pages.to_set().contains(staged_page_ptr) || staged_page_ptr == thread_page,
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr),
{
    assert(thread_staged_pages_2m_forward_wf(post.thr_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_thread_staged_pages_2m_forward_wf; reveal(thread_staged_pages_2m_forward_wf); };
    publish_staged_container_root_eof_thread_staged_pages_2m_backward_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    reveal(thread_staged_pages_2m_wf);
}

#[verifier::spinoff_prover]
pub broadcast proof fn publish_staged_container_root_eof_thread_staged_pages_2m_backward_at(
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
    thread_ptr: RwLockThreadPtr,
    page_ptr: PagePtr,
)
    requires
        pre.inv(),
        pre.thr_mp.dom().contains(current_thread_ptr),
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
        post.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr),
        forall|staged_page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(staged_page_ptr)]
            #![trigger funding_pages.to_set().contains(staged_page_ptr)]
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(staged_page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(staged_page_ptr) <==> new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    scheduler_page,
                    cpu_set_page,
                    process_page,
                    pagetable_page,
                    l4_page,
                ).contains(staged_page_ptr) || funding_pages.to_set().contains(staged_page_ptr) || staged_page_ptr == thread_page,
        forall|page_ptr: PagePtr|
            #![trigger pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        #![trigger
            publish_staged_container_root_kernel_state_framing(
                pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)
        ]
        {
            &&& page_ptr_valid(page_ptr)
            &&& post.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned2m { thread_ptr })
        },
{
    assert(thread_staged_pages_2m_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    assert(thread_staged_pages_4k_wf(pre.thr_mp, pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); reveal(thread_staged_pages_wf); };
    assert(hugepage_2m_wf(pre.pg_arr)) by { reveal(KernelK::inv); reveal(KernelK::memory_management_inv); };
    assert(hugepage_2m_tail_forward_wf(pre.pg_arr)) by { reveal(hugepage_2m_wf); };
    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
    assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(container_page));
    assert(pre.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(pcid_allocator_page));
    assert(pre.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_2m_wf); };
    assert(pre.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr })) by { reveal(thread_staged_pages_2m_wf); };
    assert(post.thr_mp.dom() == pre.thr_mp.dom()) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(LockedMap::unchanged_except); };
    assert(post.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty()) by { reveal(publish_staged_container_root_kernel_state_framing); };
    assert(thread_ptr != current_thread_ptr);
    assert(pre.thr_mp.dom().contains(thread_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(LockedMap::unchanged_except); };
    assert(pre.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(LockedMap::unchanged_except); };
    assert(pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned2m { thread_ptr })) by { reveal(thread_staged_pages_2m_wf); };
    assert(page_ptr_valid(page_ptr)) by { reveal(thread_staged_pages_2m_wf); };
    page_ptr_valid_imply_page_index_valid();
    assert(!funding_pages.to_set().contains(page_ptr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(!page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_ptr2page_index(page_ptr))) by {
        if page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_ptr2page_index(page_ptr)) {
            assert(spec_page_index_merge_2m_valid(page_ptr2page_index(container_page), page_ptr2page_index(page_ptr),)) by { reveal(page_2m_tail_indices); };
            assert(pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Merged2m) by { reveal(hugepage_2m_tail_forward_wf); };
        }
    };
    assert(!page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr2page_index(page_ptr))) by {
        if page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr2page_index(page_ptr)) {
            assert(spec_page_index_merge_2m_valid(page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(page_ptr),)) by { reveal(page_2m_tail_indices); };
            assert(pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Merged2m) by { reveal(hugepage_2m_tail_forward_wf); };
        }
    };
    assert(page_ptr != container_page);
    assert(page_ptr != pcid_allocator_page);
    assert(!new_container_bootstrap_4k_pages(
        allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
    ).contains(page_ptr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(!page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(container_page)).contains(page_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(container_page), 512, page_ptr,);
            assert(page_ptr2page_index(page_ptr) != page_ptr2page_index(container_page)) by { page_ptr2page_index_injective(); };
            assert(page_2m_tail_indices(page_ptr2page_index(container_page)).contains(page_ptr2page_index(page_ptr))) by { reveal(page_2m_tail_indices); };
        }
    };
    assert(!page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr)) by {
        if page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr) {
            reveal(page_2m_all_ptrs);
            page_2m_ptr_prefix_member_bounds(page_ptr2page_index(pcid_allocator_page), 512, page_ptr,);
            assert(page_ptr2page_index(page_ptr) != page_ptr2page_index(pcid_allocator_page)) by { page_ptr2page_index_injective(); };
            assert(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(page_ptr2page_index(page_ptr))) by { reveal(page_2m_tail_indices); };
        }
    };
    assert(!new_container_moved_pages(
        container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page,
    ).contains(page_ptr)) by {
        reveal(new_container_moved_pages); page_ptr2page_index_injective();
    };
    page_ptr_roundtrip();
    publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k, page_ptr2page_index(page_ptr),
    );
}
}
