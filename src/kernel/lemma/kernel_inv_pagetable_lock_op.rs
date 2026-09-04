use vstd::prelude::*;
use crate::*;

verus! {

pub open spec fn pagetable_invariant_fields_unchanged(
    pre: PageTableLockedMap,
    post: PageTableLockedMap,
) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|pt_ptr: RwLockPageTableRoot|
        #![trigger pre.spec_index(pt_ptr).view()]
        #![trigger post.spec_index(pt_ptr).view()]
        pre.dom().contains(pt_ptr) ==>
            post.spec_index(pt_ptr).view()
                == pre.spec_index(pt_ptr).view()
}

pub proof fn pagetable_lock_op_preserves_invariant_fields(
    pre: PageTableLockedMap,
    post: PageTableLockedMap,
    changed: RwLockPageTableRoot,
)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view()
            == pre.spec_index(changed).view(),
    ensures
        pagetable_invariant_fields_unchanged(pre, post),
{
}

pub proof fn lemma_no_change_imply_pagetable_perms_wf_forall()
    ensures
        forall|pre: PageTableLockedMap,
            post: PageTableLockedMap,
            changed: RwLockPageTableRoot|
            #![trigger
                pagetable_perms_wf(pre),
                pagetable_perms_wf(post),
                post.spec_index(changed)
            ]
            pagetable_perms_wf(pre)
            && pre.dom().contains(changed)
            && post.perms_wf()
            && post.unchanged_except(&pre, changed)
            && post.spec_index(changed).inv()
            ==> pagetable_perms_wf(post),
{
    reveal(pagetable_perms_wf);
}

pub proof fn lemma_no_change_imply_process_pagetable_match_for_pagetable_fields_forall()
    ensures
        forall|process_map: ProcessLockedMap,
            pre: PageTableLockedMap,
            post: PageTableLockedMap|
            #![trigger
                process_pagetable_match(process_map, pre),
                process_pagetable_match(process_map, post)
            ]
            process_pagetable_match(process_map, pre)
            && pagetable_invariant_fields_unchanged(pre, post)
            ==> process_pagetable_match(process_map, post),
{
    reveal(process_pagetable_match);
}

pub proof fn lemma_no_change_imply_page_pagetable_wf_for_pagetable_fields_forall()
    ensures
        forall|pre: PageTableLockedMap,
            post: PageTableLockedMap,
            page_array: PageLockedArray|
            #![trigger
                page_pagetable_wf(pre, page_array),
                page_pagetable_wf(post, page_array)
            ]
            page_pagetable_wf(pre, page_array)
            && pagetable_invariant_fields_unchanged(pre, post)
            ==> page_pagetable_wf(post, page_array),
{
    reveal(mapped_4k_page_pagetable_wf);
    reveal(mapped_2m_page_pagetable_wf);
    reveal(mapped_1g_page_pagetable_wf);
}

pub proof fn lemma_no_change_imply_container_process_page_pagetable_wf_for_pagetable_fields_forall()
    ensures
        forall|container_map: ContainerLockedMap,
            process_map: ProcessLockedMap,
            pre: PageTableLockedMap,
            post: PageTableLockedMap,
            page_array: PageLockedArray|
            #![trigger
                container_process_page_pagetable_wf(
                    container_map, process_map, pre, page_array,
                ),
                container_process_page_pagetable_wf(
                    container_map, process_map, post, page_array,
                )
            ]
            container_process_page_pagetable_wf(
                container_map, process_map, pre, page_array,
            )
            && process_pagetable_match(process_map, pre)
            && page_pagetable_wf(pre, page_array)
            && container_page_owner_wf(container_map, page_array)
            && pagetable_invariant_fields_unchanged(pre, post)
            ==> container_process_page_pagetable_wf(
                container_map, process_map, post, page_array,
            ),
{
    reveal(container_process_page_pagetable_wf);
    reveal(process_pagetable_match);
    reveal(container_page_owner_wf);
    reveal(mapped_4k_page_pagetable_wf);
    reveal(mapped_2m_page_pagetable_wf);
    reveal(mapped_1g_page_pagetable_wf);
}

pub proof fn lemma_no_change_imply_pagetable_pages_wf_for_pagetable_fields_forall()
    ensures
        forall|pre: PageTableLockedMap,
            post: PageTableLockedMap,
            page_array: PageLockedArray|
            #![trigger
                pagetable_pages_wf(pre, page_array),
                pagetable_pages_wf(post, page_array)
            ]
            pagetable_pages_wf(pre, page_array)
            && pagetable_invariant_fields_unchanged(pre, post)
            ==> pagetable_pages_wf(post, page_array),
{
    reveal(pagetable_pages_wf);
}

pub proof fn lemma_no_change_imply_cpu_dirty_map_wf_for_pagetable_fields_forall()
    ensures
        forall|container_map: ContainerLockedMap,
            process_map: ProcessLockedMap,
            cpu_array: CpuLockedArray,
            cpu_tlb: CpuTLB,
            pre: PageTableLockedMap,
            post: PageTableLockedMap|
            #![trigger
                cpu_dirty_map_wf(
                    container_map, process_map, cpu_array, cpu_tlb, pre,
                ),
                cpu_dirty_map_wf(
                    container_map, process_map, cpu_array, cpu_tlb, post,
                )
            ]
            cpu_dirty_map_wf(
                container_map, process_map, cpu_array, cpu_tlb, pre,
            )
            && pagetable_invariant_fields_unchanged(pre, post)
            ==> cpu_dirty_map_wf(
                container_map, process_map, cpu_array, cpu_tlb, post,
            ),
{
    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
}

pub proof fn lemma_no_change_imply_tlb_wf_spec_for_pagetable_fields_forall()
    ensures
        forall|cpu_tlb: CpuTLB,
            cpu_array: CpuLockedArray,
            pre: PageTableLockedMap,
            post: PageTableLockedMap|
            #![trigger
                tlb_wf_spec(cpu_tlb, pre, cpu_array),
                tlb_wf_spec(cpu_tlb, post, cpu_array)
            ]
            tlb_wf_spec(cpu_tlb, pre, cpu_array)
            && pagetable_invariant_fields_unchanged(pre, post)
            ==> tlb_wf_spec(cpu_tlb, post, cpu_array),
{
    reveal(tlb_wf_spec);
}

}
