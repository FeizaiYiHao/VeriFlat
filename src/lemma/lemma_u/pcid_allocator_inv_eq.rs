use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

#[verifier::opaque]
pub open spec fn container_pcid_allocator_fields_unchanged(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|c_ptr: RwLockContainerPtr|
        #![trigger post.spec_index(c_ptr)]
        pre.dom().contains(c_ptr)
        ==>
        post.spec_index(c_ptr).view_rodata()
            == pre.spec_index(c_ptr).view_rodata()
}

#[verifier::opaque]
pub open spec fn process_pcid_fields_unchanged(
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.spec_index(p_ptr)]
        pre.dom().contains(p_ptr)
        ==>
        {
            &&& post.spec_index(p_ptr).view_rodata()
                == pre.spec_index(p_ptr).view_rodata()
            &&& post.spec_index(p_ptr).view().pcid
                == pre.spec_index(p_ptr).view().pcid
        }
}

pub proof fn container_pcid_allocator_wf_preserved_for_fields_unchanged(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
    pcid_allocator_map: PcidAllocatorLockedMap,
)
    requires
        container_pcid_allocator_wf(pre, pcid_allocator_map),
        container_pcid_allocator_fields_unchanged(pre, post),
    ensures
        container_pcid_allocator_wf(post, pcid_allocator_map),
{
    reveal(container_pcid_allocator_fields_unchanged);
    reveal(container_pcid_allocator_wf);
}

pub proof fn process_pcid_allocator_wf_preserved_for_fields_unchanged(
    container_map: ContainerLockedMap,
    pre: ProcessLockedMap,
    post: ProcessLockedMap,
    pcid_allocator_map: PcidAllocatorLockedMap,
)
    requires
        process_pcid_allocator_wf(container_map, pre, pcid_allocator_map),
        process_pcid_fields_unchanged(pre, post),
    ensures
        process_pcid_allocator_wf(container_map, post, pcid_allocator_map),
{
    reveal(process_pcid_fields_unchanged);
    reveal(process_pcid_allocator_wf);
}

pub proof fn process_pcid_allocator_wf_preserved_for_container_fields_unchanged(
    pre: ContainerLockedMap,
    post: ContainerLockedMap,
    process_map: ProcessLockedMap,
    pcid_allocator_map: PcidAllocatorLockedMap,
)
    requires
        process_pcid_allocator_wf(pre, process_map, pcid_allocator_map),
        container_process_wf(pre, process_map),
        container_pcid_allocator_fields_unchanged(pre, post),
    ensures
        process_pcid_allocator_wf(post, process_map, pcid_allocator_map),
{
    reveal(container_pcid_allocator_fields_unchanged);
    reveal(container_process_wf);
    reveal(process_pcid_allocator_wf);
}

pub proof fn pcid_allocator_pages_wf_preserved_for_page_payloads_unchanged(
    pre: PageLockedArray,
    post: PageLockedArray,
    pcid_allocator_map: PcidAllocatorLockedMap,
)
    requires
        pcid_allocator_pages_wf(pre, pcid_allocator_map),
        post.payloads_unchanged(&pre),
    ensures
        pcid_allocator_pages_wf(post, pcid_allocator_map),
{
    reveal(LockedArray::payloads_unchanged);
    reveal(pcid_allocator_pages_wf);
}

pub proof fn pcid_allocator_pages_wf_preserved_for_page_state_eq(
    pre: PageLockedArray,
    post: PageLockedArray,
    pre_pcid_allocator_map: PcidAllocatorLockedMap,
    post_pcid_allocator_map: PcidAllocatorLockedMap,
)
    requires
        pcid_allocator_pages_wf(pre, pre_pcid_allocator_map),
        post_pcid_allocator_map.dom() == pre_pcid_allocator_map.dom(),
        forall|page_index: PageIndex|
            #![trigger post.spec_index(page_index).view().view().state]
            page_index_wf(page_index)
            && {
                ||| pre.spec_index(page_index).view().view().state
                    matches PageState::Allocated2m {
                        state: Allocated2MPageState::AsPcidAllocator,
                    }
                ||| post.spec_index(page_index).view().view().state
                    matches PageState::Allocated2m {
                        state: Allocated2MPageState::AsPcidAllocator,
                    }
            }
            ==>
            post.spec_index(page_index).view().view().state
                == pre.spec_index(page_index).view().view().state,
    ensures
        pcid_allocator_pages_wf(post, post_pcid_allocator_map),
{
    reveal(pcid_allocator_pages_wf);
}

}
