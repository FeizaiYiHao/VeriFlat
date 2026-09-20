use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_eof_subsystems_inv(
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
        post.subsystems_inv(),
{
    assert(pre.subsystems_inv()) by { reveal(KernelK::inv); };
    assert(pagetable_perms_wf(post.pt_mp)) by { reveal(pagetable_perms_wf); reveal(pagetables_inv); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
    assert(containers_inv(post.ctn_mp)) by {
        assert(container_perms_wf(pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::subsystems_inv); };
        reveal(containers_inv);
        reveal(container_perms_wf);
        reveal(publish_staged_container_root_kernel_state_framing);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(container_tree_fields_wf(post.ctn_mp)) by {
        assert(container_tree_fields_wf(pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::subsystems_inv); reveal(container_perms_wf); };
        assert(container_perms_wf(pre.ctn_mp)) by { reveal(KernelK::inv); reveal(KernelK::subsystems_inv); };
        container_perms_wf_at(pre.ctn_mp, parent_container_ptr);
        reveal(container_tree_fields_wf);
        assert(!pre.ctn_mp.spec_index(parent_container_ptr).view().children.view().contains(container_page)) by {
            reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(container_tree_wf); reveal(container_children_parent_wf);
        };
        assert(!pre.ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().contains(parent_container_ptr)) by {
            reveal(KernelK::inv); reveal(KernelK::process_management_inv); reveal(container_tree_wf); reveal(container_uppertree_seq_wf);
        };
        reveal(publish_staged_container_root_kernel_state_framing);
        reveal(Seq::no_duplicates);
        reveal(Seq::contains);
        seq_push_lemma::<RwLockContainerPtr>();
        seq_push_unique_lemma::<RwLockContainerPtr>();
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); };
    assert(process_perms_wf(post.prc_mp)) by {
        reveal(process_perms_wf); reveal(process_tree_fields_wf); reveal(publish_staged_container_root_kernel_state_framing);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(thread_perms_wf(post.thr_mp)) by {
        reveal(thread_perms_wf); reveal(threads_inv); reveal(thread_temp_alloc_empty_unless_wlocked);
        reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_endpoint_transit_only_when_wlocked);
        reveal(publish_staged_container_root_kernel_state_framing);
    };
    assert(scheduler_perms_wf(post.sched_mp)) by {
        reveal(scheduler_perms_wf); reveal(publish_staged_container_root_kernel_state_framing);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(cpu_set_perms_wf(post.cpu_set_mp)) by { reveal(cpu_set_perms_wf); reveal(publish_staged_container_root_kernel_state_framing); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
    assert(pcid_allocator_perms_wf(post.pcid_allc_mp)) by {
        reveal(pcid_allocator_perms_wf); reveal(publish_staged_container_root_kernel_state_framing);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(allocator_perms_wf(post.allc_4k_mp)) by {
        reveal(allocator_perms_wf); reveal(publish_staged_container_root_kernel_state_framing);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(allocator_perms_wf(post.allc_2m_mp)) by {
        reveal(allocator_perms_wf); reveal(publish_staged_container_root_kernel_state_framing);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(allocator_perms_wf(post.allc_1g_mp)) by {
        reveal(allocator_perms_wf); reveal(publish_staged_container_root_kernel_state_framing);
        broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::subsystems_inv); reveal(publish_staged_container_root_kernel_state_framing); };
}


}
