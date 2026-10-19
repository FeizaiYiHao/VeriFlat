use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) proof fn eof_process_kernel_pages_owner_as_process(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
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
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_with_iommu_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        forall|page_index: PageIndex|
            #![trigger post.pg_arr.spec_index(page_index).view().view().owning_container]
            index_valid(NUM_PAGES, page_index) ==> {
                let page = post.pg_arr.spec_index(page_index).view().view();
                let ptr = page_index2page_ptr(page_index);
                page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess }) ==> page.owning_container == post.prc_mp.spec_index(ptr).view_rodata().view().owning_container
            },
{
    reveal(create_process_with_iommu_from_staged_pages_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective();
    reveal(process_kernel_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match);
}

pub(super) proof fn eof_process_kernel_pages_owner_pagetable_root(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
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
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_with_iommu_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        forall|page_index: PageIndex|
            #![trigger post.pg_arr.spec_index(page_index).view().view().owning_container]
            index_valid(NUM_PAGES, page_index) ==> {
                let page = post.pg_arr.spec_index(page_index).view().view();
                let ptr = page_index2page_ptr(page_index);
                page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } }) ==> page.owning_container == post.prc_mp.spec_index(post.pt_mp.spec_index(ptr).view().proc_ptr).view_rodata().view().owning_container
            },
{
    reveal(create_process_with_iommu_from_staged_pages_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective();
    reveal(process_kernel_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match);
}

pub(super) proof fn eof_process_kernel_pages_owner_iommu_root(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
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
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_with_iommu_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        forall|page_index: PageIndex|
            #![trigger post.pg_arr.spec_index(page_index).view().view().owning_container]
            index_valid(NUM_PAGES, page_index) ==> {
                let page = post.pg_arr.spec_index(page_index).view().view();
                let ptr = page_index2page_ptr(page_index);
                page.state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } }) ==> page.owning_container == post.prc_mp.spec_index(post.it_mp.spec_index(ptr).view().proc_ptr).view_rodata().view().owning_container
            },
{
    reveal(create_process_with_iommu_from_staged_pages_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective();
    reveal(process_kernel_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match);
}

pub(super) proof fn eof_process_kernel_pages_owner_pagetable_node(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
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
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_with_iommu_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        forall|page_index: PageIndex|
            #![trigger post.pg_arr.spec_index(page_index).view().view().owning_container]
            index_valid(NUM_PAGES, page_index) ==> {
                let page = post.pg_arr.spec_index(page_index).view().view();
                let state = page.state->Allocated4k_state;
                page.state is Allocated4k && state is PageTable && state->PageTable_table_type == PT_TYPE ==> page.owning_container == post.prc_mp.spec_index(post.pt_mp.spec_index(state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
            },
{
    reveal(create_process_with_iommu_from_staged_pages_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective();
    reveal(process_kernel_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match);
}

pub(super) proof fn eof_process_kernel_pages_owner_iommu_node(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
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
        pre.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        create_process_with_iommu_from_staged_pages_eof_transition_framing(pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid),
    ensures
        forall|page_index: PageIndex|
            #![trigger post.pg_arr.spec_index(page_index).view().view().owning_container]
            index_valid(NUM_PAGES, page_index) ==> {
                let page = post.pg_arr.spec_index(page_index).view().view();
                let state = page.state->Allocated4k_state;
                page.state is Allocated4k && state is PageTable && state->PageTable_table_type == IOMMU_TYPE ==> page.owning_container == post.prc_mp.spec_index(post.it_mp.spec_index(state->PageTable_pagetable_root).view().proc_ptr).view_rodata().view().owning_container
            },
{
    reveal(create_process_with_iommu_from_staged_pages_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective();
    reveal(process_kernel_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match);
}
}
