use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn create_process_with_iommu_from_staged_pages_eof(
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
        !pre.pt_mp.dom().contains(pagetable_page_ptr),
        !pre.it_mp.dom().contains(iommu_table_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container
            == container_ptr,
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container
            == container_ptr,
        pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 5,
        pre.thr_mp.spec_index(staging_thread_ptr)
            .view().temp_alloc_cache_4k.view()
            =~= set![
                process_page_ptr,
                pagetable_page_ptr,
                l4_page_ptr,
                iommu_table_page_ptr,
                iommu_l4_page_ptr,
            ],
        pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator
            == pcid_allocator_ptr,
        pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
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
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr))
            .view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr))
            .view().view().owning_container == container_ptr,
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
        post.inv(),
        kernel_u_create_process_with_iommu_changed(
            kernel_k_to_kernel_u(pre),
            kernel_k_to_kernel_u(post),
            parent_ptr,
            process_page_ptr,
        ),
        kernel_k_to_kernel_u(post) != kernel_k_to_kernel_u(pre),
{
    create_process_with_iommu_from_staged_pages_eof_subsystems_inv(
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
    create_process_with_iommu_from_staged_pages_eof_memory_management_inv(
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
    create_process_with_iommu_from_staged_pages_eof_process_management_inv(
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
    assert(iommu_root_table_process_wf(&post.irt, post.prc_mp, post.it_mp)) by {
        reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
        reveal(iommu_root_table_process_wf);
    };
    assert(process_pci_function_ownership_wf(&post.irt, post.prc_mp)) by {
        reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
        reveal(process_pci_function_ownership_wf);
    };
    assert(iommu_tlb_wf_spec(
        post.iommu_tlb,
        &post.irt,
        post.prc_mp,
        post.it_mp,
    )) by {
        reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
        reveal(iommu_tlb_wf_spec);
    };
    assert(cpu_dirty_map_wf(
        post.ctn_mp,
        post.cpu_set_mp,
        post.prc_mp,
        post.cpu_arr,
        post.cpu_tlb,
        post.pt_mp,
        post.pcid_needflush,
    )) by {
        reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
        reveal(cpu_dirty_map_contains_container_processes);
        reveal(container_cpu_wf);
        reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(
        post.cpu_tlb,
        post.pt_mp,
        post.cpu_arr,
        post.pcid_needflush,
    )) by {
        reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
        reveal(tlb_wf_spec);
    };
    assert(post.inv()) by {
        reveal(KernelK::inv);
    };
    assert(kernel_u_create_process_with_iommu_changed(
        kernel_k_to_kernel_u(pre),
        kernel_k_to_kernel_u(post),
        parent_ptr,
        process_page_ptr,
    )) by {
        reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
        reveal(kernel_u_create_process_with_iommu_changed);
        reveal(kernel_k_to_kernel_u);
        reveal(process_pagetable_match);
        reveal(process_iommu_table_match);
    };
    assert(kernel_k_to_kernel_u(post) != kernel_k_to_kernel_u(pre)) by {
        reveal(kernel_u_create_process_with_iommu_changed);
    };
}


}
