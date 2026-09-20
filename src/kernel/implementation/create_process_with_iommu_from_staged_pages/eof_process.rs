use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn create_process_with_iommu_from_staged_pages_eof_process_tree_invariants(
    pre: KernelK,
    post: KernelK,
    process_page_ptr: PagePtr,
    pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr,
    iommu_l4_page_ptr: PagePtr,
    parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    pcid: Pcid,
)
    requires
        pre.inv(),
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container
            == container_ptr,
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container
            == container_ptr,
        pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator
            == pcid_allocator_ptr,
        pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        create_process_with_iommu_from_staged_pages_kernel_state_framing(
            pre,
            post,
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
            iommu_table_page_ptr,
            iommu_l4_page_ptr,
            parent_ptr,
            staging_thread_ptr,
            container_ptr,
            pcid_allocator_ptr,
            pcid,
        ),
        post.prc_mp.spec_index(process_page_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
        post.ctn_mp.spec_index(container_ptr).inv(),
        post.thr_mp.spec_index(staging_thread_ptr).inv(),
        post.pcid_allc_mp.spec_index(pcid_allocator_ptr).inv(),
    ensures
        process_perms_wf(post.prc_mp),
        container_perms_wf(post.ctn_mp),
        thread_perms_wf(post.thr_mp),
        pcid_allocator_perms_wf(post.pcid_allc_mp),
        container_tree_wf(post.rt_ctn, post.ctn_mp),
        container_process_wf(post.ctn_mp, post.prc_mp),
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
{
    reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
    assert(pre.subsystems_inv()) by {
        reveal(KernelK::inv);
    };
    assert(pre.process_management_inv()) by {
        reveal(KernelK::inv);
    };
    let ancestors =
        pre.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr);
    let root_process = pre.ctn_mp.spec_index(container_ptr).view().root_process;
    let process_tree_dom =
        pre.ctn_mp.spec_index(container_ptr).view().owned_processes.view();

    assert(process_perms_wf(pre.prc_mp)) by {
        reveal(KernelK::subsystems_inv);
    };
    assert(per_container_process_tree_wf(pre.ctn_mp, pre.prc_mp)) by {
        reveal(KernelK::process_management_inv);
    };
    assert(container_process_wf(pre.ctn_mp, pre.prc_mp)) by {
        reveal(KernelK::process_management_inv);
    };
    assert(process_tree_wf(
        root_process,
        process_tree_dom,
        pre.prc_mp,
    )) by {
        reveal(container_process_wf);
        reveal(per_container_process_tree_wf);
    };
    assert(post.prc_mp.perms_wf()) by {
        reveal(LockedMap::perms_wf);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(process_tree_fields_wf(post.prc_mp)) by {
        assert(process_tree_fields_wf(pre.prc_mp)) by {
            reveal(process_perms_wf);
        };
        assert(!pre.prc_mp.spec_index(parent_ptr)
            .view().children.view().contains(process_page_ptr)) by {
            reveal(container_process_wf);
            reveal(process_children_parent_wf);
        };
        assert(!pre.prc_mp.spec_index(parent_ptr)
            .view_ghost().uppertree_seq.view().contains(parent_ptr)) by {
            reveal(container_process_wf);
            reveal(process_uppertree_seq_wf);
        };
        process_perms_wf_at(pre.prc_mp, parent_ptr);
        reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
        reveal(container_process_wf);
        reveal(process_children_parent_wf);
        reveal(process_uppertree_seq_wf);
        reveal(process_tree_fields_wf);
        reveal(Seq::no_duplicates);
        seq_push_lemma::<RwLockProcessPtr>();
        seq_push_unique_lemma::<RwLockProcessPtr>();
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(process_perms_wf(post.prc_mp)) by {
        reveal(process_perms_wf);
        reveal(process_tree_fields_wf);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(container_perms_wf(post.ctn_mp)) by {
        reveal(container_perms_wf);
        reveal(containers_inv);
        reveal(container_tree_fields_wf);
    };
    assert(thread_perms_wf(post.thr_mp)) by {
        reveal(thread_perms_wf);
        reveal(thread_temp_alloc_empty_unless_wlocked);
        reveal(thread_free_quota_pending_empty_unless_wlocked);
    };
    assert(pcid_allocator_perms_wf(post.pcid_allc_mp)) by {
        reveal(pcid_allocator_perms_wf);
    };
    assert(process_add_child_ensures(
        root_process,
        process_tree_dom,
        pre.prc_mp,
        post.prc_mp,
        parent_ptr,
        process_page_ptr,
    )) by {
        reveal(process_add_child_ensures);
        reveal(per_container_process_tree_wf);
        reveal(container_process_wf);
        reveal(process_perms_wf);
        reveal(LinkedList::wf_value_list);
        ancestors.to_set_ensures();
        seq_push_lemma::<RwLockProcessPtr>();
        broadcast use vstd::map::lemma_map_insert_domain;
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    process_add_child_preserves_tree_wf(
        root_process,
        process_tree_dom,
        pre.prc_mp,
        post.prc_mp,
        parent_ptr,
        process_page_ptr,
    );

    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by {
        container_no_change_to_tree_fields_imply_wf(
            pre.rt_ctn,
            pre.ctn_mp,
            post.ctn_mp,
        );
    };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by {
        reveal(container_process_wf);
        reveal(LockedMap::unchanged_except);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
        assert(process_tree_wf(
            post.ctn_mp.spec_index(container_ptr).view().root_process,
            post.ctn_mp.spec_index(container_ptr).view().owned_processes.view(),
            post.prc_mp,
        )) by {
            broadcast use vstd::set::lemma_set_insert_same;
            broadcast use vstd::set::lemma_set_insert_different;
        };
        reveal(per_container_process_tree_wf);
        reveal(container_process_wf);
        reveal(process_uppertree_seq_wf);
        process_no_change_to_tree_fields_imply_wf_forall();
        ancestors.to_set_ensures();
        reveal(LockedMap::unchanged_except);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn create_process_with_iommu_from_staged_pages_eof_process_management_inv(
    pre: KernelK,
    post: KernelK,
    process_page_ptr: PagePtr,
    pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr,
    iommu_l4_page_ptr: PagePtr,
    parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    pcid: Pcid,
)
    requires
        pre.inv(),
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        create_process_with_iommu_from_staged_pages_kernel_state_framing(
            pre,
            post,
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
            iommu_table_page_ptr,
            iommu_l4_page_ptr,
            parent_ptr,
            staging_thread_ptr,
            container_ptr,
            pcid_allocator_ptr,
            pcid,
        ),
        post.prc_mp.spec_index(process_page_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
        post.ctn_mp.spec_index(container_ptr).inv(),
        post.thr_mp.spec_index(staging_thread_ptr).inv(),
        post.pcid_allc_mp.spec_index(pcid_allocator_ptr).inv(),
    ensures
        post.process_management_inv(),
{
    create_process_with_iommu_from_staged_pages_eof_process_tree_invariants(
        pre,
        post,
        process_page_ptr,
        pagetable_page_ptr,
        l4_page_ptr,
        iommu_table_page_ptr,
        iommu_l4_page_ptr,
        parent_ptr,
        staging_thread_ptr,
        container_ptr,
        pcid_allocator_ptr,
        pcid,
    );
    reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
    assert(post.process_management_inv()) by {
        assert(post.ctn_mp.spec_index(post.rt_ctn)
            .view().root_process_in_processes()) by {
            reveal(container_root_wf);
        };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by {
            reveal(container_endpoint_wf);
        };
        assert(container_cpu_wf(
            post.ctn_mp,
            post.cpu_set_mp,
            post.cpu_arr,
        )) by {
            reveal(container_cpu_wf);
        };
        assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by {
            reveal(thread_endpoint_ref_counter_wf);
        };
        assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by {
            reveal(thread_endpoint_queue_wf);
        };
        assert(thread_caller_callee_wf(post.thr_mp)) by {
            reveal(thread_caller_callee_wf);
        };
        assert(container_thread_endpoint_wf(
            post.ctn_mp,
            post.thr_mp,
            post.ep_mp,
        )) by {
            reveal(container_thread_endpoint_wf);
            reveal(container_endpoint_wf);
            reveal(thread_endpoint_ref_counter_wf);
            reveal(thread_endpoint_queue_wf);
        };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by {
            reveal(container_scheduler_wf);
        };
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by {
            reveal(container_cpu_set_wf);
        };
        assert(container_pcid_allocator_wf(
            post.ctn_mp,
            post.pcid_allc_mp,
        )) by {
            reveal(container_pcid_allocator_wf);
        };
        assert(process_pcid_allocator_wf(
            post.ctn_mp,
            post.prc_mp,
            post.pcid_allc_mp,
        )) by {
            reveal(process_pcid_allocator_wf);
            reveal(container_process_wf);
            reveal(container_pcid_allocator_wf);
            broadcast use vstd::set::lemma_set_insert_same;
            broadcast use vstd::set::lemma_set_insert_different;
        };
        assert(container_thread_scheduler_wf(
            post.ctn_mp,
            post.thr_mp,
            post.sched_mp,
        )) by {
            reveal(container_thread_scheduler_wf);
            reveal(container_thread_wf);
            reveal(container_scheduler_wf);
        };
        assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by {
            reveal(container_thread_wf);
        };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by {
            reveal(process_cpu_wf);
        };
        assert(process_thread_wf(post.prc_mp, post.thr_mp)) by {
            reveal(process_empty_lists_wlocked);
            reveal(process_thread_wf);
        };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by {
            reveal(thread_cpu_wf);
        };
    };
}


}
