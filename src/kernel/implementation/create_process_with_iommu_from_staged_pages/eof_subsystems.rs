use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn create_process_with_iommu_from_staged_pages_eof_subsystems_inv(
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
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container
            == container_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr),
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
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().inv(),
        post.pt_mp.perms_wf(),
        post.pt_mp.spec_index(pagetable_page_ptr).inv(),
        post.it_mp.perms_wf(),
        post.it_mp.spec_index(iommu_table_page_ptr).inv(),
        post.prc_mp.perms_wf(),
        post.prc_mp.spec_index(process_page_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
        post.ctn_mp.perms_wf(),
        post.ctn_mp.spec_index(container_ptr).inv(),
        post.thr_mp.perms_wf(),
        post.thr_mp.spec_index(staging_thread_ptr).inv(),
        post.pcid_allc_mp.perms_wf(),
        post.pcid_allc_mp.spec_index(pcid_allocator_ptr).inv(),
    ensures
        post.subsystems_inv(),
{
    reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
    assert(pre.subsystems_inv()) by {
        reveal(KernelK::inv);
    };
    let process_page_index = page_ptr2page_index(process_page_ptr);
    let pagetable_page_index = page_ptr2page_index(pagetable_page_ptr);
    let l4_page_index = page_ptr2page_index(l4_page_ptr);
    let iommu_table_page_index = page_ptr2page_index(iommu_table_page_ptr);
    let iommu_l4_page_index = page_ptr2page_index(iommu_l4_page_ptr);
    assert(index_valid(NUM_PAGES, process_page_index)
        && index_valid(NUM_PAGES, pagetable_page_index)
        && index_valid(NUM_PAGES, l4_page_index)
        && index_valid(NUM_PAGES, iommu_table_page_index)
        && index_valid(NUM_PAGES, iommu_l4_page_index)) by {
        page_ptr_valid_imply_page_index_valid();
    };
    assert(process_page_index != pagetable_page_index
        && process_page_index != l4_page_index
        && process_page_index != iommu_table_page_index
        && process_page_index != iommu_l4_page_index
        && pagetable_page_index != l4_page_index
        && pagetable_page_index != iommu_table_page_index
        && pagetable_page_index != iommu_l4_page_index
        && l4_page_index != iommu_table_page_index
        && l4_page_index != iommu_l4_page_index
        && iommu_table_page_index != iommu_l4_page_index) by {
        page_ptr2page_index_neq(process_page_ptr, pagetable_page_ptr);
        page_ptr2page_index_neq(process_page_ptr, l4_page_ptr);
        page_ptr2page_index_neq(process_page_ptr, iommu_table_page_ptr);
        page_ptr2page_index_neq(process_page_ptr, iommu_l4_page_ptr);
        page_ptr2page_index_neq(pagetable_page_ptr, l4_page_ptr);
        page_ptr2page_index_neq(pagetable_page_ptr, iommu_table_page_ptr);
        page_ptr2page_index_neq(pagetable_page_ptr, iommu_l4_page_ptr);
        page_ptr2page_index_neq(l4_page_ptr, iommu_table_page_ptr);
        page_ptr2page_index_neq(l4_page_ptr, iommu_l4_page_ptr);
        page_ptr2page_index_neq(iommu_table_page_ptr, iommu_l4_page_ptr);
    };
    assert(pagetable_perms_wf(post.pt_mp)) by {
        reveal(pagetable_perms_wf);
        reveal(pagetables_inv);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(iommu_table_perms_wf(post.it_mp)) by {
        reveal(iommu_table_perms_wf);
        broadcast use vstd::set::lemma_set_insert_same;
        broadcast use vstd::set::lemma_set_insert_different;
    };
    assert(page_array_wf(post.pg_arr)) by {
        reveal(page_array_wf);
    };
    assert(process_tree_fields_wf(post.prc_mp)) by {
        assert(process_tree_fields_wf(pre.prc_mp)) by {
            reveal(process_perms_wf);
        };
        reveal(container_process_wf);
        assert(!pre.prc_mp.spec_index(parent_ptr)
            .view().children.view().contains(process_page_ptr)) by {
            reveal(per_container_process_tree_wf);
            reveal(process_children_parent_wf);
        };
        assert(!pre.prc_mp.spec_index(parent_ptr)
            .view_ghost().uppertree_seq.view().contains(parent_ptr)) by {
            reveal(per_container_process_tree_wf);
            reveal(process_uppertree_seq_wf);
        };
        process_perms_wf_at(pre.prc_mp, parent_ptr);
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
        reveal(threads_inv);
        reveal(thread_temp_alloc_empty_unless_wlocked);
        reveal(thread_free_quota_pending_empty_unless_wlocked);
        reveal(thread_endpoint_transit_only_when_wlocked);
    };
    assert(pcid_allocator_perms_wf(post.pcid_allc_mp)) by {
        reveal(pcid_allocator_perms_wf);
    };
    assert(post.default_pagetable_wf()) by {
        reveal(KernelK::default_pagetable_wf);
    };
    assert(post.subsystems_inv()) by {
        reveal(KernelK::subsystems_inv);
    };
}


}
