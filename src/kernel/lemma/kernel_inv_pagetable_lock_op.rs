use vstd::prelude::*;
use crate::*;

verus! {
/// Every page table keeps its payload, so with an unchanged window half every whole table is unchanged.
pub open spec fn pagetable_invariant_fields_unchanged(pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|pt_ptr: RwLockPageTableRoot|
        #![trigger pre.spec_index(pt_ptr).view()]
        #![trigger post.spec_index(pt_ptr).view()]
        pre.dom().contains(pt_ptr) ==> post.spec_index(pt_ptr).view() == pre.spec_index(pt_ptr).view()
    &&& forall|pt_ptr: RwLockPageTableRoot|
        #![trigger pagetable_c(pre, pt_lower, pt_ptr)]
        #![trigger pagetable_c(post, pt_lower, pt_ptr)]
        pre.dom().contains(pt_ptr) ==> pagetable_c(post, pt_lower, pt_ptr) == pagetable_c(pre, pt_lower, pt_ptr)
}

pub proof fn pagetable_lock_op_preserves_invariant_fields(pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap, changed: RwLockPageTableRoot)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view() == pre.spec_index(changed).view(),
    ensures
        pagetable_invariant_fields_unchanged(pre, post, pt_lower),
{
}

pub proof fn lemma_pagetable_perms_wf_preserved_for_lock_op_forall()
    ensures
        forall|pre: PageTableLockedMap, post: PageTableLockedMap, changed: RwLockPageTableRoot|
            #![trigger pagetable_perms_wf(pre), pagetable_perms_wf(post), post.spec_index(changed)]
            pagetable_perms_wf(pre) && pre.dom().contains(changed) && post.perms_wf() && post.unchanged_except(&pre, changed) && post.spec_index(changed).inv() ==> pagetable_perms_wf(post),
{ reveal(pagetable_perms_wf); }

pub proof fn lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall()
    ensures
        forall|process_map: ProcessLockedMap, pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap|
            #![trigger process_pagetable_match(process_map, pre), process_pagetable_match(process_map, post), pagetable_invariant_fields_unchanged(pre, post, pt_lower)]
            process_pagetable_match(process_map, pre) && pagetable_invariant_fields_unchanged(pre, post, pt_lower) ==> process_pagetable_match(process_map, post),
{ reveal(process_pagetable_match); }

pub proof fn lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall()
    ensures
        forall|pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray|
            #![trigger page_pagetable_wf(pre, pt_lower, page_array), page_pagetable_wf(post, pt_lower, page_array)]
            page_pagetable_wf(pre, pt_lower, page_array) && pagetable_invariant_fields_unchanged(pre, post, pt_lower) ==> page_pagetable_wf(post, pt_lower, page_array),
{ reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); }

pub proof fn lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall()
    ensures
        forall|container_map: ContainerLockedMap, process_map: ProcessLockedMap, pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray|
            #![trigger container_process_page_pagetable_wf(container_map, process_map, pre, page_array), container_process_page_pagetable_wf(container_map, process_map, post, page_array), pagetable_invariant_fields_unchanged(pre, post, pt_lower)]
            container_process_page_pagetable_wf(container_map, process_map, pre, page_array) && process_pagetable_match(process_map, pre) && page_pagetable_wf(pre, pt_lower, page_array)
                && container_page_owner_wf(container_map, page_array) && pagetable_invariant_fields_unchanged(pre, post, pt_lower)
                ==> container_process_page_pagetable_wf(container_map, process_map, post, page_array),
{ reveal(container_process_page_pagetable_wf); }

pub proof fn lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall()
    ensures
        forall|pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray|
            #![trigger pagetable_pages_wf(pre, pt_lower, page_array), pagetable_pages_wf(post, pt_lower, page_array)]
            pagetable_pages_wf(pre, pt_lower, page_array) && pagetable_invariant_fields_unchanged(pre, post, pt_lower) ==> pagetable_pages_wf(post, pt_lower, page_array),
{ reveal(pagetable_pages_wf); }

pub proof fn lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall()
    ensures
        forall|container_map: ContainerLockedMap, cpu_set_map: CpuSetLockedMap, process_map: ProcessLockedMap, cpu_array: CpuLockedArray, needflush: PcidNeedFlushArray, cpu_tlb: CpuTLB, pre: PageTableLockedMap, post: PageTableLockedMap,
            pt_lower: PageTableLowerMap|
            #![trigger cpu_dirty_map_wf(container_map, cpu_set_map, process_map, cpu_array, cpu_tlb, pre, needflush), cpu_dirty_map_wf(container_map, cpu_set_map, process_map, cpu_array, cpu_tlb, post, needflush), pagetable_invariant_fields_unchanged(pre, post, pt_lower)]
            cpu_dirty_map_wf(container_map, cpu_set_map, process_map, cpu_array, cpu_tlb, pre, needflush) && pagetable_invariant_fields_unchanged(pre, post, pt_lower)
                ==> cpu_dirty_map_wf(container_map, cpu_set_map, process_map, cpu_array, cpu_tlb, post, needflush),
{ reveal(cpu_dirty_map_contains_pagetable_pcid_match); }

pub proof fn lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall()
    ensures
        forall|cpu_tlb: CpuTLB, needflush: PcidNeedFlushArray, cpu_array: CpuLockedArray, pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap|
            #![trigger tlb_wf_spec(cpu_tlb, pre, pt_lower, cpu_array, needflush), tlb_wf_spec(cpu_tlb, post, pt_lower, cpu_array, needflush)]
            tlb_wf_spec(cpu_tlb, pre, pt_lower, cpu_array, needflush) && pagetable_invariant_fields_unchanged(pre, post, pt_lower) ==> tlb_wf_spec(cpu_tlb, post, pt_lower, cpu_array, needflush),
{ reveal(tlb_wf_spec); }
}
