use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

pub proof fn lemma_container_pcid_allocator_wf_preserved_for_container_invariant_fields_forall()
    ensures
        forall|pre: ContainerLockedMap,
            post: ContainerLockedMap,
            pcid_allocator_map: PcidAllocatorLockedMap|
            #![trigger
                container_pcid_allocator_wf(pre, pcid_allocator_map),
                container_pcid_allocator_wf(post, pcid_allocator_map)
            ]
            container_pcid_allocator_wf(pre, pcid_allocator_map)
            && container_invariant_fields_unchanged(pre, post)
            ==> container_pcid_allocator_wf(post, pcid_allocator_map),
{
    reveal(container_pcid_allocator_wf);
}

pub proof fn lemma_process_pcid_allocator_wf_preserved_for_container_invariant_fields_forall()
    ensures
        forall|pre: ContainerLockedMap,
            post: ContainerLockedMap,
            process_map: ProcessLockedMap,
            pcid_allocator_map: PcidAllocatorLockedMap|
            #![trigger
                process_pcid_allocator_wf(pre, process_map, pcid_allocator_map),
                process_pcid_allocator_wf(post, process_map, pcid_allocator_map)
            ]
            process_pcid_allocator_wf(pre, process_map, pcid_allocator_map)
            && container_process_wf(pre, process_map)
            && container_invariant_fields_unchanged(pre, post)
            ==> process_pcid_allocator_wf(post, process_map, pcid_allocator_map),
{
    reveal(process_pcid_allocator_wf);
    reveal(container_process_wf);
}

pub proof fn lemma_process_pcid_allocator_wf_preserved_for_process_quota_4k_framed_fields_forall()
    ensures
        forall|container_map: ContainerLockedMap,
            pre: ProcessLockedMap,
            post: ProcessLockedMap,
            pcid_allocator_map: PcidAllocatorLockedMap|
            #![trigger
                process_pcid_allocator_wf(container_map, pre, pcid_allocator_map),
                process_pcid_allocator_wf(container_map, post, pcid_allocator_map)
            ]
            process_pcid_allocator_wf(container_map, pre, pcid_allocator_map)
            && process_quota_4k_framed_fields_unchanged(pre, post)
            ==> process_pcid_allocator_wf(container_map, post, pcid_allocator_map),
{
    reveal(process_pcid_allocator_wf);
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
            index_valid(NUM_PAGES, page_index)
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
