use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) proof fn create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_as_process(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        page_ptr_valid(iommu_table_pg_ptr),
        page_ptr_valid(iommu_l4_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        process_pg_ptr != iommu_table_pg_ptr,
        process_pg_ptr != iommu_l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != iommu_table_pg_ptr,
        pagetable_pg_ptr != iommu_l4_pg_ptr,
        l4_pg_ptr != iommu_table_pg_ptr,
        l4_pg_ptr != iommu_l4_pg_ptr,
        iommu_table_pg_ptr != iommu_l4_pg_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, true, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        forall|pg_idx: PageIndex|
            #![trigger post.pg_arr.spec_index(pg_idx).view().view().owning_container]
            index_valid(NUM_PAGES, pg_idx) ==> {
                let page = post.pg_arr.spec_index(pg_idx).view().view();
                let ptr = page_index2page_ptr(pg_idx);
                page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess }) ==> page.owning_container == post.prc_mp.spec_index(ptr).view_rodata().view().owning_container
            },
{
    reveal(create_process_from_staged_pages_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective();
    reveal(process_object_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
}

pub(super) proof fn create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_pagetable_root(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        page_ptr_valid(iommu_table_pg_ptr),
        page_ptr_valid(iommu_l4_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        process_pg_ptr != iommu_table_pg_ptr,
        process_pg_ptr != iommu_l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != iommu_table_pg_ptr,
        pagetable_pg_ptr != iommu_l4_pg_ptr,
        l4_pg_ptr != iommu_table_pg_ptr,
        l4_pg_ptr != iommu_l4_pg_ptr,
        iommu_table_pg_ptr != iommu_l4_pg_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, true, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        forall|pg_idx: PageIndex|
            #![trigger post.pg_arr.spec_index(pg_idx).view().view().owning_container]
            index_valid(NUM_PAGES, pg_idx) ==> {
                let page = post.pg_arr.spec_index(pg_idx).view().view();
                let ptr = page_index2page_ptr(pg_idx);
                page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } }) ==> page.owning_container == post.prc_mp.spec_index(post.pt_mp.spec_index(ptr).view().proc_ptr).view_rodata().view().owning_container
            },
{
    hide(Seq::contains); reveal(create_process_from_staged_pages_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective();
    reveal(process_object_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
}

pub(super) proof fn create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_iommu_root(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        page_ptr_valid(iommu_table_pg_ptr),
        page_ptr_valid(iommu_l4_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        process_pg_ptr != iommu_table_pg_ptr,
        process_pg_ptr != iommu_l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != iommu_table_pg_ptr,
        pagetable_pg_ptr != iommu_l4_pg_ptr,
        l4_pg_ptr != iommu_table_pg_ptr,
        l4_pg_ptr != iommu_l4_pg_ptr,
        iommu_table_pg_ptr != iommu_l4_pg_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, true, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        forall|pg_idx: PageIndex|
            #![trigger post.pg_arr.spec_index(pg_idx).view().view().owning_container]
            index_valid(NUM_PAGES, pg_idx) ==> {
                let page = post.pg_arr.spec_index(pg_idx).view().view();
                let ptr = page_index2page_ptr(pg_idx);
                page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } }) ==> page.owning_container == post.prc_mp.spec_index(post.it_mp.spec_index(ptr).view().proc_ptr).view_rodata().view().owning_container
            },
{
    reveal(create_process_from_staged_pages_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective();
    reveal(process_object_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
}

pub(super) proof fn create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_pagetable_node(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        page_ptr_valid(iommu_table_pg_ptr),
        page_ptr_valid(iommu_l4_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        process_pg_ptr != iommu_table_pg_ptr,
        process_pg_ptr != iommu_l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != iommu_table_pg_ptr,
        pagetable_pg_ptr != iommu_l4_pg_ptr,
        l4_pg_ptr != iommu_table_pg_ptr,
        l4_pg_ptr != iommu_l4_pg_ptr,
        iommu_table_pg_ptr != iommu_l4_pg_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, true, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        forall|pg_idx: PageIndex|
            #![trigger post.pg_arr.spec_index(pg_idx).view().view().owning_container]
            index_valid(NUM_PAGES, pg_idx) ==> {
                let page = post.pg_arr.spec_index(pg_idx).view().view();
                let state = page.state->Allocated4k_state;
                page.state is Allocated4k && state is PageTable && state->PageTable_table_type == PT_TYPE ==> page.owning_container == post.prc_mp.spec_index(post.pt_mp.spec_index(state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
            },
{
    reveal(create_process_from_staged_pages_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective();
    reveal(process_object_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
}

pub(super) proof fn create_process_with_iommu_from_staged_pages_eof_process_kernel_pages_owner_iommu_node(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        page_ptr_valid(iommu_table_pg_ptr),
        page_ptr_valid(iommu_l4_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        process_pg_ptr != iommu_table_pg_ptr,
        process_pg_ptr != iommu_l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != iommu_table_pg_ptr,
        pagetable_pg_ptr != iommu_l4_pg_ptr,
        l4_pg_ptr != iommu_table_pg_ptr,
        l4_pg_ptr != iommu_l4_pg_ptr,
        iommu_table_pg_ptr != iommu_l4_pg_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, true, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        forall|pg_idx: PageIndex|
            #![trigger post.pg_arr.spec_index(pg_idx).view().view().owning_container]
            index_valid(NUM_PAGES, pg_idx) ==> {
                let page = post.pg_arr.spec_index(pg_idx).view().view();
                let state = page.state->Allocated4k_state;
                page.state is Allocated4k && state is PageTable && state->PageTable_table_type == IOMMU_TYPE ==> page.owning_container == post.prc_mp.spec_index(post.it_mp.spec_index(state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
            },
{
    hide(Seq::contains); reveal(create_process_from_staged_pages_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective();
    reveal(process_object_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
}
}
