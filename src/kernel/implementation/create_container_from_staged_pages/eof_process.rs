use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_container_uppertree_seq_wf(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        container_perms_wf(post.ctn_mp),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_uppertree_seq_wf(post.rt_ctn, post.ctn_mp),
{
    assert(container_tree_fields_wf(pre.ctn_mp)) by { reveal(container_perms_wf); };
    assert(container_tree_fields_wf(post.ctn_mp)) by { reveal(container_perms_wf); };
    assert(container_uppertree_seq_wf(post.rt_ctn, post.ctn_mp)) by {
        reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions); reveal(container_uppertree_seq_wf); reveal(container_tree_fields_wf);
        seq_push_implies_contains::<RwLockContainerPtr>(); seq_push_absent_implies_no_duplicates_and_index_of::<RwLockContainerPtr>();
    };
}

pub(super) proof fn publish_staged_container_root_eof_container_tree_wf(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_tree_wf(post.rt_ctn, post.ctn_mp),
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    assert(container_root_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_root_wf); };
    assert(container_children_parent_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_children_parent_wf); seq_push_implies_contains::<RwLockContainerPtr>(); };
    assert(container_linkedlist_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_linkedlist_wf); reveal(container_children_parent_wf); };
    assert(container_tree_fields_wf(pre.ctn_mp)) by { reveal(container_perms_wf); };
    assert(container_uppertree_seq_parent_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_uppertree_seq_parent_wf); reveal(container_tree_fields_wf); seq_push_implies_contains::<RwLockContainerPtr>(); };
    assert(container_subtree_set_wf(post.rt_ctn, post.ctn_mp)) by { reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_tree_fields_wf); seq_push_implies_contains::<RwLockContainerPtr>(); };
    publish_staged_container_root_eof_container_uppertree_seq_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(container_subtree_uppertree_agree_wf(post.rt_ctn, post.ctn_mp)) by {
        reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_subtree_uppertree_agree_wf);
        seq_push_implies_contains::<RwLockContainerPtr>(); seq_push_absent_implies_no_duplicates_and_index_of::<RwLockContainerPtr>();
    };
}

pub(super) proof fn publish_staged_container_root_eof_container_cpu_wf(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        container_cpu_set_wf(pre.ctn_mp, pre.cpu_set_mp),
        container_cpu_wf(pre.ctn_mp, pre.cpu_set_mp, pre.cpu_arr),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions); reveal(container_cpu_set_wf); reveal(container_cpu_wf);
}

/// The new container owns no endpoint and no thread holds a descriptor into it; every other endpoint relation is unchanged.
pub(super) proof fn publish_staged_container_root_eof_container_endpoint_relations_wf(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp),
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by {
        assert(forall|c: RwLockContainerPtr|
            #![trigger post.ctn_mp.spec_index(c).view_ghost().owned_endpoints]
            post.ctn_mp.dom().contains(c) && c != container_page ==> post.ctn_mp.spec_index(c).view_ghost().owned_endpoints == pre.ctn_mp.spec_index(c).view_ghost().owned_endpoints);
        assert(forall|e: RwLockEndpointPtr| #![trigger post.ctn_mp.spec_index(container_page).view_ghost().owned_endpoints.view().contains(e)] !post.ctn_mp.spec_index(container_page).view_ghost().owned_endpoints.view().contains(e));
        reveal(container_endpoint_wf);
    };
    assert(thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); reveal(container_thread_endpoint_wf); };
}

/// The new process owns no thread and every other process keeps its threads.
pub(super) proof fn publish_staged_container_root_eof_process_thread_wf(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures process_thread_wf(post.prc_mp, post.thrd_mp),
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    assert forall|p_ptr: RwLockProcessPtr, t_ptr: RwLockThreadPtr| #![trigger post.prc_mp.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr)]
        post.prc_mp.dom().contains(p_ptr) && post.prc_mp.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr)
        implies post.thrd_mp.dom().contains(t_ptr) && post.thrd_mp.spec_index(t_ptr).view().owning_proc == p_ptr
            && post.thrd_mp.spec_index(t_ptr).view().owning_container == post.prc_mp.spec_index(p_ptr).view_rodata().view().owning_container
            && post.thrd_mp.spec_index(t_ptr).view().container_depth == post.prc_mp.spec_index(p_ptr).view_rodata().view().container_depth
            && post.thrd_mp.spec_index(t_ptr).view().process_depth == post.prc_mp.spec_index(p_ptr).view_rodata().view().depth
            && post.thrd_mp.spec_index(t_ptr).view().proc_pagetable_ptr == post.prc_mp.spec_index(p_ptr).view().pagetable
            && post.prc_mp.spec_index(p_ptr).view().owned_threads.map().dom().contains(post.thrd_mp.spec_index(t_ptr).view().proc_linkedlist_node.addr())
            && post.prc_mp.spec_index(p_ptr).view().owned_threads.map().spec_index(post.thrd_mp.spec_index(t_ptr).view().proc_linkedlist_node.addr()) == t_ptr
            && !post.thrd_mp.spec_index(t_ptr).view().proc_linkedlist_node.is_init() by {
        reveal(process_thread_wf);
        if p_ptr == process_page { assert(post.prc_mp.spec_index(p_ptr).view().owned_threads.view().len() == 0); }
        else { assert(pre.prc_mp.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr)); }
    };
    assert forall|t_ptr: RwLockThreadPtr| #![trigger post.thrd_mp.spec_index(t_ptr).being_killed()] post.thrd_mp.dom().contains(t_ptr) && post.thrd_mp.spec_index(t_ptr).being_killed() implies {
        let process = post.prc_mp.spec_index(post.thrd_mp.spec_index(t_ptr).view().owning_proc);
        &&& post.thrd_mp.spec_index(t_ptr).locking_thread() is Write
        &&& !post.thrd_mp.spec_index(t_ptr).view().state.is_reply_waiting()
        &&& !thread_is_dangling(post.thrd_mp.spec_index(t_ptr)) ==> {
            &&& process.being_killed()
            &&& process.locking_thread() is Write
            &&& post.thrd_mp.spec_index(t_ptr).locking_thread()->Write_thread_id == process.locking_thread()->Write_thread_id
        }
    } by { reveal(process_thread_wf); assert(pre.thrd_mp.spec_index(t_ptr).being_killed()); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_thread_wf); };
}

pub(super) proof fn publish_staged_container_root_eof_container_relations_wf(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        container_thread_wf(post.ctn_mp, post.thrd_mp),
        container_process_wf(post.ctn_mp, post.prc_mp),
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp),
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp),
        container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp),
        process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp),
        process_thread_wf(post.prc_mp, post.thrd_mp),
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
    assert(container_thread_wf(post.ctn_mp, post.thrd_mp)) by { reveal(container_thread_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(process_tree_wf(process_page, set![process_page], post.prc_mp,)) by {
        reveal(process_root_wf); reveal(process_children_parent_wf); reveal(process_linkedlist_wf); reveal(process_uppertree_seq_parent_wf); reveal(process_subtree_set_wf);
        reveal(process_uppertree_seq_wf); reveal(process_subtree_uppertree_agree_wf);
    };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); reveal(container_process_wf); process_no_change_to_tree_fields_imply_wf_forall(); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
    publish_staged_container_root_eof_container_cpu_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { pcid_allocator_perms_wf_at(post.pcid_allc_mp, pcid_allocator_page); reveal(process_pcid_allocator_wf); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp,)) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
    publish_staged_container_root_eof_container_endpoint_relations_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_process_thread_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
}

pub(super) proof fn publish_staged_container_root_eof_process_management_inv(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        post.memory_management_inv(),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        post.process_management_inv(),
{
    reveal(publish_staged_container_root_eof_transition_framing);
    publish_staged_container_root_eof_container_tree_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_relations_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
    assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(thread_caller_callee_wf(post.thrd_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp); };
    assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); reveal(publish_staged_container_root_eof_preconditions); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); reveal(publish_staged_container_root_eof_preconditions); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); reveal(publish_staged_container_root_eof_preconditions); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
    assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.cpu_arr); };
}

pub(super) proof fn publish_staged_container_root_eof_direct_invariants(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        post.memory_management_inv(),
        post.process_management_inv(),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush,),
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(cpu_dirty_map_process_in_cpu_container(post.ctn_mp, post.cpu_set_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb,)) by { reveal(container_cpu_wf); reveal(cpu_dirty_map_process_in_cpu_container); };
    assert(cpu_dirty_map_proc_pcid_match(post.prc_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb,)) by { reveal(cpu_dirty_map_proc_pcid_match); };
    assert(cpu_dirty_map_pagetable_pcid_match(post.pt_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(cpu_tlb_wf); };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
}

pub(super) proof fn publish_staged_container_root_eof_iommu_invariants(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp),
        process_pci_function_ownership_wf(post.irt.view(), post.prc_mp),
        iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp),
{
    reveal(publish_staged_container_root_eof_transition_framing);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); };
}

pub(super) broadcast proof fn publish_staged_container_root_eof_container_page_owner_forward(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, c_ptr: RwLockContainerPtr, pg_ptr: PagePtr,
)
    requires
        container_owned_pages_forward_wf(pre.ctn_mp, pre.pg_arr),
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
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        post.ctn_mp.dom().contains(c_ptr),
        post.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(pg_ptr),
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(pg_ptr)
        ]
        {
            &&& page_ptr_valid(pg_ptr)
            &&& post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == c_ptr
        },
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    let moved_pages = new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).union(funding_pages.to_set());
    if c_ptr == container_page {
        assert(post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == c_ptr) by {
            if funding_pages.to_set().contains(pg_ptr) { } else {
                let container_head = page_ptr2page_index(container_page);
                let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
                reveal(new_container_moved_pages);
                if page_2m_all_ptrs(container_head).contains(pg_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
                    page_2m_ptr_prefix_member_bounds(container_head, 512, pg_ptr);
                    if page_ptr2page_index(pg_ptr) != container_head { }
                } else if page_2m_all_ptrs(pcid_allocator_head).contains(pg_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
                    page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, pg_ptr,);
                    if page_ptr2page_index(pg_ptr) != pcid_allocator_head { }
                } else { reveal(new_container_bootstrap_4k_pages); }
            }
        };
    } else if c_ptr == parent_ctn_ptr {
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
        publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_ptr2page_index(pg_ptr),
        );
    } else {
        assert(!moved_pages.contains(pg_ptr)) by { if moved_pages.contains(pg_ptr) { } };
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
        publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, page_ptr2page_index(pg_ptr),
        );
    }
}

pub(super) broadcast proof fn publish_staged_container_root_eof_container_page_owner_backward(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_pages: Seq<PagePtr>,
    allocator_quota_4k: usize, process_quota_4k: usize, pg_idx: PageIndex,
)
    requires
        container_owned_pages_backward_wf(pre.ctn_mp, pre.pg_arr),
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
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        index_valid(NUM_PAGES, pg_idx),
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(pg_idx).view().view().owning_container
        ]
        {
            let c_ptr = post.pg_arr.spec_index(pg_idx).view().view().owning_container;
            &&& post.ctn_mp.dom().contains(c_ptr)
            &&& post.ctn_mp.spec_index(c_ptr).view().owned_pages.view().contains(page_index2page_ptr(pg_idx))
        },
{
    reveal(publish_staged_container_root_eof_transition_framing); reveal(publish_staged_container_root_eof_preconditions);
    let pg_ptr = page_index2page_ptr(pg_idx);
    let moved_pages = new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).union(funding_pages.to_set());
    page_index_valid_imply_page_ptr_valid(); page_index_roundtrip();
    if moved_pages.contains(pg_ptr) {
        assert(post.pg_arr.spec_index(pg_idx).view().view().owning_container == container_page) by {
            if funding_pages.to_set().contains(pg_ptr) { } else {
                let container_head = page_ptr2page_index(container_page);
                let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
                reveal(new_container_moved_pages);
                if page_2m_all_ptrs(container_head).contains(pg_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
                    page_2m_ptr_prefix_member_bounds(container_head, 512, pg_ptr);
                    if pg_idx != container_head { }
                } else if page_2m_all_ptrs(pcid_allocator_head).contains(pg_ptr) {
                    page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
                    page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, pg_ptr,);
                    if pg_idx != pcid_allocator_head { }
                } else { reveal(new_container_bootstrap_4k_pages); }
            }
        };
    } else {
        publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, pg_idx,
        );
        let c_ptr = pre.pg_arr.spec_index(pg_idx).view().view().owning_container;
        if c_ptr == parent_ctn_ptr { } else { }
    }
}

pub(super) proof fn publish_staged_container_root_eof_container_page_owner_wf(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
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
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        container_owned_pages_wf(post.ctn_mp, post.pg_arr),
{
    assert(container_owned_pages_forward_wf(pre.ctn_mp, pre.pg_arr)) by { reveal(container_owned_pages_wf); };
    assert(container_owned_pages_backward_wf(pre.ctn_mp, pre.pg_arr)) by { reveal(container_owned_pages_wf); };
    assert(container_owned_pages_forward_wf(post.ctn_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_container_page_owner_forward; };
    assert(container_owned_pages_backward_wf(post.ctn_mp, post.pg_arr)) by { broadcast use publish_staged_container_root_eof_container_page_owner_backward; };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_owned_pages_wf); };
}

pub(super) proof fn publish_staged_container_root_eof_memory_management_inv(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
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
        funding_pages.to_set().disjoint(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page)),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        forall|pg_ptr: PagePtr| #![trigger funding_pages.to_set().contains(pg_ptr)] funding_pages.to_set().contains(pg_ptr) ==> page_ptr_valid(pg_ptr),
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        post.memory_management_inv(),
{
    hide(Seq::contains); reveal(publish_staged_container_root_eof_transition_framing);
    publish_staged_container_root_eof_container_page_owner_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    publish_staged_container_root_eof_object_pages_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_hugepage_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_container_pages_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_thread_staged_pages_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by {
        broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq; reveal(process_emptied_tables_wf); reveal(process_pagetable_wf);
    };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); reveal(process_pagetable_wf); };
    publish_staged_container_root_eof_allocator_free_pages_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_allocator_quota_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_process_kernel_pages_owner_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    publish_staged_container_root_eof_page_object_owner_wf(
        pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
        allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
        allocator_quota_4k, process_quota_4k,
    );
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        reveal(publish_staged_container_root_eof_preconditions); reveal(container_kill_retire_wf); reveal(container_uppertree_seq_wf);
        broadcast use vstd::seq_lib::lemma_seq_contains_after_push;
    };
}

/// The root process's object page, page-table root page, and L4 page belong to the new container; every other process
/// kernel page keeps its state, owner, and process.
pub(super) proof fn publish_staged_container_root_eof_process_kernel_pages_owner_wf(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
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
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
    ensures
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
{
    hide(Seq::contains); reveal(publish_staged_container_root_eof_transition_framing);
    broadcast use publish_staged_container_root_eof_unmodified_object_page_state_eq;
    page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
    reveal(process_object_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
}

/// The new container's object pages are named by the new container; every other object page keeps its state, its owner,
/// and the owner's object fields.
pub(super) proof fn publish_staged_container_root_eof_page_object_owner_wf(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
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
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        page_array_wf(post.pg_arr),
    ensures
        page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
{
    broadcast use publish_staged_container_root_eof_page_object_owner_at;
    reveal(page_object_owner_wf);
}

pub(super) broadcast proof fn publish_staged_container_root_eof_page_object_owner_at(
    pre: KernelK, post: KernelK, parent_ctn_ptr: RwLockContainerPtr, current_thrd_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_pages: Seq<PagePtr>, allocator_quota_4k: usize, process_quota_4k: usize, pg_idx: PageIndex,
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
        publish_staged_container_root_eof_transition_framing(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        publish_staged_container_root_eof_preconditions(
            pre, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k,
        ),
        page_array_wf(post.pg_arr),
        index_valid(NUM_PAGES, pg_idx),
    ensures
        #![trigger
            publish_staged_container_root_eof_transition_framing(
                pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page,
                allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
                funding_pages, allocator_quota_4k, process_quota_4k,
            ),
            post.pg_arr.spec_index(pg_idx).view().view().owning_container
        ]
        ({
            let page = post.pg_arr.spec_index(pg_idx).view().view();
            let ptr = page_index2page_ptr(pg_idx);
            let container = post.ctn_mp.spec_index(page.owning_container);
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }) ==> container.view_ghost().owned_threads.view().contains(ptr)
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }) ==> container.view_ghost().owned_endpoints.view().contains(ptr)
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsScheduler }) ==> container.view_rodata().view().scheduler == ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet }) ==> container.view_rodata().view().cpu_set == ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }) ==> container.view_rodata().view().allocator_ptr_4k == ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }) ==> container.view_rodata().view().allocator_ptr_2m == ptr
            &&& page.state == (PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }) ==> container.view_rodata().view().allocator_ptr_1g == ptr
            &&& page.state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer }) ==> page.owning_container == ptr
            &&& page.state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }) ==> container.view_rodata().view().pcid_allocator == ptr
            &&& page.state is Unavailable || page.is_io_page ==> container.view_rodata().view().parent is None
            &&& page.state is Owned4k || page.state is Owned2m || page.state is Owned1g ==> {
                let thrd_ptr = if page.state is Owned4k { page.state->Owned4k_thread_ptr } else if page.state is Owned2m { page.state->Owned2m_thread_ptr } else { page.state->Owned1g_thread_ptr };
                let thread = post.thrd_mp.spec_index(thrd_ptr);
                &&& post.thrd_mp.dom().contains(thrd_ptr)
                &&& page.owning_container == thread.view().owning_container || container.locking_thread() is Write && thread.locking_thread() is Write
                    && container.locking_thread()->Write_thread_id == thread.locking_thread()->Write_thread_id && !container.being_killed()
            }
        }),
{
    hide(Seq::contains); reveal(publish_staged_container_root_eof_transition_framing);
    let pg_ptr = page_index2page_ptr(pg_idx);
    let moved_pages = new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).union(funding_pages.to_set());
    if moved_pages.contains(pg_ptr) {
        page_index_valid_imply_page_ptr_valid(); page_index_roundtrip(); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_array_wf_at(post.pg_arr, pg_idx);
        if funding_pages.to_set().contains(pg_ptr) { } else {
            let container_head = page_ptr2page_index(container_page);
            let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
            reveal(new_container_moved_pages);
            if page_2m_all_ptrs(container_head).contains(pg_ptr) {
                page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
                page_2m_ptr_prefix_member_bounds(container_head, 512, pg_ptr);
                if pg_idx != container_head { }
            } else if page_2m_all_ptrs(pcid_allocator_head).contains(pg_ptr) {
                page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
                page_2m_ptr_prefix_member_bounds(pcid_allocator_head, 512, pg_ptr);
                if pg_idx != pcid_allocator_head { }
            } else { reveal(Seq::contains); reveal(new_container_bootstrap_4k_pages); }
        }
    } else {
        publish_staged_container_root_eof_page_fields_eq_outside_moved_pages(
            pre, post, parent_ctn_ptr, current_thrd_ptr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
            allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_pages,
            allocator_quota_4k, process_quota_4k, pg_idx,
        );
        page_object_owner_wf_at(pre.ctn_mp, pre.thrd_mp, pre.pg_arr, pg_idx); container_owned_pages_wf_backward_at(pre.ctn_mp, pre.pg_arr, pg_idx);
        reveal(publish_staged_container_root_eof_preconditions);
    }
}
}
