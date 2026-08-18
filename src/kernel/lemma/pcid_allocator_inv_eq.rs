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
    assert(container_pcid_allocator_wf(post, pcid_allocator_map)) by {
        reveal(container_pcid_allocator_fields_unchanged);
        reveal(container_pcid_allocator_wf);
    };
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
    assert(process_pcid_allocator_wf(container_map, post, pcid_allocator_map)) by {
        reveal(process_pcid_fields_unchanged);
        reveal(process_pcid_allocator_wf);
    };
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
    assert(process_pcid_allocator_wf(post, process_map, pcid_allocator_map)) by {
        reveal(container_pcid_allocator_fields_unchanged);
        reveal(container_process_wf);
        reveal(process_pcid_allocator_wf);
    };
}

pub proof fn lemma_no_change_imply_container_pcid_allocator_wf_forall()
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
    assert forall|pre: ContainerLockedMap,
        post: ContainerLockedMap,
        pcid_allocator_map: PcidAllocatorLockedMap| #![auto]
        container_pcid_allocator_wf(pre, pcid_allocator_map)
        && container_invariant_fields_unchanged(pre, post)
    implies
        container_pcid_allocator_wf(post, pcid_allocator_map)
    by {
        assert(container_pcid_allocator_fields_unchanged(pre, post)) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_pcid_allocator_fields_unchanged);
        };
        container_pcid_allocator_wf_preserved_for_fields_unchanged(pre, post, pcid_allocator_map);
    };
}

pub proof fn lemma_no_change_imply_process_pcid_allocator_wf_for_container_fields_forall()
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
    assert forall|pre: ContainerLockedMap,
        post: ContainerLockedMap,
        process_map: ProcessLockedMap,
        pcid_allocator_map: PcidAllocatorLockedMap| #![auto]
        process_pcid_allocator_wf(pre, process_map, pcid_allocator_map)
        && container_process_wf(pre, process_map)
        && container_invariant_fields_unchanged(pre, post)
    implies
        process_pcid_allocator_wf(post, process_map, pcid_allocator_map)
    by {
        assert(container_pcid_allocator_fields_unchanged(pre, post)) by {
            reveal(container_invariant_fields_unchanged);
            reveal(container_pcid_allocator_fields_unchanged);
        };
        process_pcid_allocator_wf_preserved_for_container_fields_unchanged(pre, post, process_map, pcid_allocator_map);
    };
}

pub proof fn lemma_no_change_imply_process_pcid_allocator_wf_forall()
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
    assert forall|container_map: ContainerLockedMap,
        pre: ProcessLockedMap,
        post: ProcessLockedMap,
        pcid_allocator_map: PcidAllocatorLockedMap| #![auto]
        process_pcid_allocator_wf(container_map, pre, pcid_allocator_map)
        && process_quota_4k_framed_fields_unchanged(pre, post)
    implies
        process_pcid_allocator_wf(container_map, post, pcid_allocator_map)
    by {
        assert(process_pcid_fields_unchanged(pre, post)) by {
            reveal(process_pcid_fields_unchanged);
        };
        process_pcid_allocator_wf_preserved_for_fields_unchanged(container_map, pre, post, pcid_allocator_map);
    };
}

pub proof fn pcid_allocator_pages_wf_preserved_for_page_lock_change(
    pre: PageLockedArray,
    post: PageLockedArray,
    pcid_allocator_map: PcidAllocatorLockedMap,
    changed_page: PageIndex,
)
    requires
        pcid_allocator_pages_wf(pre, pcid_allocator_map),
        index_valid(NUM_PAGES, changed_page),
        post.unchanged_except(&pre, changed_page),
    ensures
        pcid_allocator_pages_wf(post, pcid_allocator_map),
{
    assert(pcid_allocator_pages_wf(post, pcid_allocator_map)) by {
        reveal(pcid_allocator_pages_wf);
    };
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
    assert(pcid_allocator_pages_wf(post, post_pcid_allocator_map)) by {
        reveal(pcid_allocator_pages_wf);
    };
}

}
