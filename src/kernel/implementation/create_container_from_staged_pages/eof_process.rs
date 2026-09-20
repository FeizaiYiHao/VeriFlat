use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_per_container_process_tree_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_process_wf(post.ctn_mp, post.prc_mp),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
{
    assert(per_container_process_tree_wf(pre.ctn_mp, pre.prc_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
    assert(process_tree_wf(process_page, set![process_page], post.prc_mp,)) by {
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(KernelK::subsystems_inv);
        reveal(process_perms_wf);
        reveal(process_tree_wf);
        reveal(process_root_wf);
        reveal(process_children_parent_wf);
        reveal(process_linkedlist_wf);
        reveal(process_children_depth_wf);
        reveal(process_subtree_set_wf);
        reveal(process_uppertree_seq_wf);
        reveal(process_subtree_set_exclusive);
        broadcast use vstd::set::lemma_set_empty_len;
        broadcast use vstd::set::lemma_set_insert_len;
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
        reveal(publish_staged_container_root_kernel_state_framing); reveal(per_container_process_tree_wf); reveal(container_process_wf);
        process_no_change_to_tree_fields_imply_wf_forall(); broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_process_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_process_wf(post.ctn_mp, post.prc_mp),
{
    assert(container_process_wf(pre.ctn_mp, pre.prc_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by {
        reveal(publish_staged_container_root_kernel_state_framing); reveal(container_process_wf);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_process_thread_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        process_thread_wf(post.prc_mp, post.thr_mp),
{
    assert(process_thread_wf(pre.prc_mp, pre.thr_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
    assert(process_empty_lists_wlocked(post.prc_mp)) by {
        assert(process_empty_lists_wlocked(pre.prc_mp)) by { reveal(process_thread_wf); };
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(KernelK::subsystems_inv);
        reveal(process_perms_wf);
        reveal(process_empty_lists_wlocked);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by {
        reveal(publish_staged_container_root_kernel_state_framing); reveal(process_thread_wf); reveal(process_empty_lists_wlocked);
        reveal(LockedMap::unchanged_except); broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_thread_scheduler_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        container_thread_wf(post.ctn_mp, post.thr_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp,),
{
    assert(container_thread_scheduler_wf(pre.ctn_mp, pre.thr_mp, pre.sched_mp,)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp,)) by {
        reveal(publish_staged_container_root_kernel_state_framing); reveal(container_thread_wf); reveal(container_scheduler_wf);
        reveal(container_thread_scheduler_wf); broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_subtree_set_exclusive(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_subtree_set_wf(post.rt_ctn, post.ctn_mp),
        container_uppertree_seq_wf(post.rt_ctn, post.ctn_mp),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_subtree_set_exclusive(post.rt_ctn, post.ctn_mp),
{
    assert(container_subtree_set_exclusive(pre.rt_ctn, pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(container_tree_wf); };
    assert(container_tree_fields_wf(pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::subsystems_inv); reveal(container_perms_wf); };
    assert(container_tree_fields_wf(post.ctn_mp)) by { reveal(KernelK::subsystems_inv); reveal(container_perms_wf); };
    assert(container_subtree_set_exclusive(post.rt_ctn, post.ctn_mp)) by {
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(container_subtree_set_wf);
        reveal(container_uppertree_seq_wf);
        reveal(container_subtree_set_exclusive);
        reveal(container_tree_fields_wf);
        seq_push_lemma::<RwLockContainerPtr>();
        seq_push_unique_lemma::<RwLockContainerPtr>();
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_uppertree_seq_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_uppertree_seq_wf(post.rt_ctn, post.ctn_mp),
{
    assert(container_uppertree_seq_wf(pre.rt_ctn, pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(container_tree_wf); };
    assert(container_tree_fields_wf(pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::subsystems_inv); reveal(container_perms_wf); };
    assert(container_tree_fields_wf(post.ctn_mp)) by { reveal(KernelK::subsystems_inv); reveal(container_perms_wf); };
    let child_uppers = post.ctn_mp.spec_index(container_page).view_ghost().uppertree_seq.view();
    reveal(publish_staged_container_root_kernel_state_framing);
    reveal(container_tree_fields_wf);
    assert(container_uppertree_seq_wf(post.rt_ctn, post.ctn_mp)) by {
        reveal(publish_staged_container_root_kernel_state_framing); reveal(container_uppertree_seq_wf); reveal(container_tree_fields_wf);
        seq_push_lemma::<RwLockContainerPtr>(); seq_push_unique_lemma::<RwLockContainerPtr>();
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_subtree_set_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_subtree_set_wf(post.rt_ctn, post.ctn_mp),
{
    assert(container_subtree_set_wf(pre.rt_ctn, pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(container_tree_wf); };
    assert(container_uppertree_seq_wf(pre.rt_ctn, pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(container_tree_wf); };
    assert(container_tree_fields_wf(pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::subsystems_inv); reveal(container_perms_wf); };
    assert(container_subtree_set_wf(post.rt_ctn, post.ctn_mp)) by {
        reveal(publish_staged_container_root_kernel_state_framing); reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf);
        reveal(container_tree_fields_wf); reveal(Seq::contains); seq_push_lemma::<RwLockContainerPtr>();
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_children_depth_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_children_depth_wf(post.rt_ctn, post.ctn_mp),
{
    assert(container_children_depth_wf(pre.rt_ctn, pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(container_tree_wf); };
    assert(container_children_depth_wf(post.rt_ctn, post.ctn_mp)) by {
        assert(container_tree_fields_wf(pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::subsystems_inv); reveal(container_perms_wf); };
        let child_uppers = pre.ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr);
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(container_children_depth_wf);
        reveal(container_tree_fields_wf);
        seq_push_lemma::<RwLockContainerPtr>();
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_tree_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_tree_wf(post.rt_ctn, post.ctn_mp),
{
    assert(container_tree_wf(pre.rt_ctn, pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
    assert(container_root_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_root_wf); };
    assert(container_children_parent_wf(post.rt_ctn, post.ctn_mp)) by {
        reveal(publish_staged_container_root_kernel_state_framing); reveal(container_children_parent_wf);
        seq_push_lemma::<RwLockContainerPtr>(); broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(containers_linkedlist_wf(post.rt_ctn, post.ctn_mp)) by {
        assert(containers_linkedlist_wf(pre.rt_ctn, pre.ctn_mp)) by { reveal(container_tree_wf); };
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(containers_linkedlist_wf);
        reveal(container_children_parent_wf);
        seq_push_lemma::<RwLockContainerPtr>();
        broadcast use vstd::map::lemma_map_insert_domain;
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    publish_staged_container_root_eof_container_children_depth_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_subtree_set_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_uppertree_seq_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_subtree_set_exclusive(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_tree_wf); };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_pcid_allocator_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp),
{
    assert(container_pcid_allocator_wf(pre.ctn_mp, pre.pcid_allc_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by {
        reveal(publish_staged_container_root_kernel_state_framing); reveal(container_pcid_allocator_wf);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_cpu_set_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
{
    assert(container_cpu_set_wf(pre.ctn_mp, pre.cpu_set_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by {
        reveal(publish_staged_container_root_kernel_state_framing); reveal(container_cpu_set_wf);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_cpu_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
{
    assert(container_cpu_wf(pre.ctn_mp, pre.cpu_set_mp, pre.cpu_arr)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by {
        reveal(publish_staged_container_root_kernel_state_framing); reveal(container_cpu_set_wf); reveal(container_cpu_wf);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_thread_endpoint_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
{
    assert(container_thread_endpoint_wf(pre.ctn_mp, pre.thr_mp, pre.ep_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
        assert(thread_perms_wf(post.thr_mp)) by { reveal(KernelK::subsystems_inv); };
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(thread_endpoint_ref_counter_wf);
        reveal(container_endpoint_wf);
        reveal(container_thread_endpoint_wf);
        reveal(LockedMap::unchanged_except);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_process_pcid_allocator_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        container_process_wf(post.ctn_mp, post.prc_mp),
        container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp),
{
    assert(process_pcid_allocator_wf(pre.ctn_mp, pre.prc_mp, pre.pcid_allc_mp)) by { reveal(KernelK::inv); reveal(KernelK::process_management_inv); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by {
        assert(pcid_allocator_perms_wf(post.pcid_allc_mp)) by { reveal(KernelK::subsystems_inv); };
        pcid_allocator_perms_wf_at(post.pcid_allc_mp, pcid_allocator_page);
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(process_pcid_allocator_wf);
        reveal(container_process_wf);
        reveal(container_pcid_allocator_wf);
        broadcast use vstd::set_lib::lemma_set_is_empty_len0;
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_process_management_inv(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        post.memory_management_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        post.process_management_inv(),
{
    publish_staged_container_root_eof_container_tree_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(post.ctn_mp.spec_index(post.rt_ctn).view().root_process_in_processes()) by { reveal(container_root_wf); };
    publish_staged_container_root_eof_container_process_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_per_container_process_tree_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); };
    publish_staged_container_root_eof_container_cpu_set_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_cpu_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    publish_staged_container_root_eof_container_thread_endpoint_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
    publish_staged_container_root_eof_container_pcid_allocator_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_process_pcid_allocator_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
    publish_staged_container_root_eof_container_thread_scheduler_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
    publish_staged_container_root_eof_process_thread_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
    assert(post.process_management_inv()) by { reveal(KernelK::process_management_inv); };
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_cpu_dirty_map_wf(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        post.memory_management_inv(),
        post.process_management_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush,),
{
    assert(cpu_dirty_map_wf(pre.ctn_mp, pre.cpu_set_mp, pre.prc_mp, pre.cpu_arr, pre.cpu_tlb, pre.pt_mp, pre.pcid_needflush,)) by { reveal(KernelK::inv); };
    assert(cpu_dirty_map_contains_container_processes(post.ctn_mp, post.cpu_set_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb,)) by {
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(KernelK::process_management_inv); };
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(container_cpu_wf);
        reveal(cpu_dirty_map_contains_container_processes);
    };
    assert(cpu_dirty_map_proc_pcid_match(post.prc_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb,)) by {
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(KernelK::process_management_inv); };
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(cpu_dirty_map_proc_pcid_match);
    };
    assert(cpu_not_in_dirty_map_imply_not_in_tlb(post.cpu_arr, post.cpu_tlb)) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); };
    assert(cpu_dirty_map_contains_pagetable_pcid_match(
        post.pt_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb,
    )) by { reveal(publish_staged_container_root_kernel_state_framing); reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush,));
}

#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_direct_invariants(
    pre: KernelK, post: KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        post.memory_management_inv(),
        post.process_management_inv(),
        publish_staged_container_root_kernel_state_framing(
            pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        iommu_root_table_process_wf(&post.irt, post.prc_mp, post.it_mp),
        process_pci_function_ownership_wf(&post.irt, post.prc_mp),
        iommu_tlb_wf_spec(post.iommu_tlb, &post.irt, post.prc_mp, post.it_mp),
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush,),
        tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush),
{
    assert(iommu_root_table_process_wf(&post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(&post.irt, post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, &post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); };
    publish_staged_container_root_eof_cpu_dirty_map_wf(
        pre, post, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
}
