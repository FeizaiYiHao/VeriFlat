use vstd::prelude::*;
use crate::*;

verus! {
/// Every page table keeps its payload, so with an unchanged window half every whole table is unchanged.
pub open spec fn pagetable_invariant_fields_unchanged(pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap) -> bool {
    &&& pre.dom() =~= post.dom()
    &&& forall|pt_ptr: RwLockPageTableRoot| #![trigger pre.spec_index(pt_ptr).view()] #![trigger post.spec_index(pt_ptr).view()] pre.dom().contains(pt_ptr) ==> post.spec_index(pt_ptr).view()
        == (PageTableHigher { lower_backup: post.spec_index(pt_ptr).view().lower_backup, ..pre.spec_index(pt_ptr).view() })
    &&& forall|pt_ptr: RwLockPageTableRoot|
        #![trigger whole_pagetable(pre, pt_lower, pt_ptr)]
        #![trigger whole_pagetable(post, pt_lower, pt_ptr)]
        pre.dom().contains(pt_ptr) ==> whole_pagetable(post, pt_lower, pt_ptr) == (WholePageTable { higher: post.spec_index(pt_ptr).view(), ..whole_pagetable(pre, pt_lower, pt_ptr) })
    &&& forall|pt_ptr: RwLockPageTableRoot| #![trigger whole_pagetable(pre, pt_lower, pt_ptr).page_closure()] #![trigger whole_pagetable(post, pt_lower, pt_ptr).page_closure()]
        pre.dom().contains(pt_ptr) ==> whole_pagetable(post, pt_lower, pt_ptr).page_closure() == whole_pagetable(pre, pt_lower, pt_ptr).page_closure()
    &&& forall|pt_ptr: RwLockPageTableRoot| #![trigger whole_pagetable(pre, pt_lower, pt_ptr).mapping_4k()] #![trigger whole_pagetable(post, pt_lower, pt_ptr).mapping_4k()]
        pre.dom().contains(pt_ptr) ==> whole_pagetable(post, pt_lower, pt_ptr).mapping_4k() == whole_pagetable(pre, pt_lower, pt_ptr).mapping_4k()
    &&& forall|pt_ptr: RwLockPageTableRoot| #![trigger whole_pagetable(pre, pt_lower, pt_ptr).mapping_2m()] #![trigger whole_pagetable(post, pt_lower, pt_ptr).mapping_2m()]
        pre.dom().contains(pt_ptr) ==> whole_pagetable(post, pt_lower, pt_ptr).mapping_2m() == whole_pagetable(pre, pt_lower, pt_ptr).mapping_2m()
    &&& forall|pt_ptr: RwLockPageTableRoot| #![trigger whole_pagetable(pre, pt_lower, pt_ptr).mapping_1g()] #![trigger whole_pagetable(post, pt_lower, pt_ptr).mapping_1g()]
        pre.dom().contains(pt_ptr) ==> whole_pagetable(post, pt_lower, pt_ptr).mapping_1g() == whole_pagetable(pre, pt_lower, pt_ptr).mapping_1g()
    &&& forall|pt_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
        #![trigger whole_pagetable(pre, pt_lower, pt_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        #![trigger whole_pagetable(post, pt_lower, pt_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        pre.dom().contains(pt_ptr) && whole_pagetable(pre, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
            ==> whole_pagetable(post, pt_lower, pt_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(pre, pt_lower, pt_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|pt_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index|
        #![trigger whole_pagetable(pre, pt_lower, pt_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
        #![trigger whole_pagetable(post, pt_lower, pt_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
        pre.dom().contains(pt_ptr) && whole_pagetable(pre, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            ==> whole_pagetable(post, pt_lower, pt_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(pre, pt_lower, pt_ptr).spec_held_2m_l2(l4i, l3i, l2i)
    &&& forall|pt_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index|
        #![trigger whole_pagetable(pre, pt_lower, pt_ptr).spec_held_1g_l3(l4i, l3i)]
        #![trigger whole_pagetable(post, pt_lower, pt_ptr).spec_held_1g_l3(l4i, l3i)]
        pre.dom().contains(pt_ptr) && whole_pagetable(pre, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
            ==> whole_pagetable(post, pt_lower, pt_ptr).spec_held_1g_l3(l4i, l3i) == whole_pagetable(pre, pt_lower, pt_ptr).spec_held_1g_l3(l4i, l3i)
    &&& forall|pt_ptr: RwLockPageTableRoot, l4i: L4Index|
        #![trigger whole_pagetable(pre, pt_lower, pt_ptr).spec_resolve_mapping_l4(l4i)]
        #![trigger whole_pagetable(post, pt_lower, pt_ptr).spec_resolve_mapping_l4(l4i)]
        pre.dom().contains(pt_ptr) && whole_pagetable(pre, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i)
            ==> whole_pagetable(post, pt_lower, pt_ptr).spec_resolve_mapping_l4(l4i) == whole_pagetable(pre, pt_lower, pt_ptr).spec_resolve_mapping_l4(l4i)
    &&& forall|pt_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index|
        #![trigger whole_pagetable(pre, pt_lower, pt_ptr).spec_resolve_mapping_l3(l4i, l3i)]
        #![trigger whole_pagetable(post, pt_lower, pt_ptr).spec_resolve_mapping_l3(l4i, l3i)]
        pre.dom().contains(pt_ptr) && whole_pagetable(pre, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
            ==> whole_pagetable(post, pt_lower, pt_ptr).spec_resolve_mapping_l3(l4i, l3i) == whole_pagetable(pre, pt_lower, pt_ptr).spec_resolve_mapping_l3(l4i, l3i)
    &&& forall|pt_ptr: RwLockPageTableRoot, l4i: L4Index|
        #![trigger whole_pagetable(pre, pt_lower, pt_ptr).spec_held_l4(l4i)]
        #![trigger whole_pagetable(post, pt_lower, pt_ptr).spec_held_l4(l4i)]
        pre.dom().contains(pt_ptr) && whole_pagetable(pre, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i)
            ==> whole_pagetable(post, pt_lower, pt_ptr).spec_held_l4(l4i) == whole_pagetable(pre, pt_lower, pt_ptr).spec_held_l4(l4i)
    &&& forall|pt_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index|
        #![trigger whole_pagetable(pre, pt_lower, pt_ptr).spec_held_l3(l4i, l3i)]
        #![trigger whole_pagetable(post, pt_lower, pt_ptr).spec_held_l3(l4i, l3i)]
        pre.dom().contains(pt_ptr) && whole_pagetable(pre, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
            ==> whole_pagetable(post, pt_lower, pt_ptr).spec_held_l3(l4i, l3i) == whole_pagetable(pre, pt_lower, pt_ptr).spec_held_l3(l4i, l3i)
    &&& forall|pt_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
        #![trigger whole_pagetable(pre, pt_lower, pt_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        #![trigger whole_pagetable(post, pt_lower, pt_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        pre.dom().contains(pt_ptr) && whole_pagetable(pre, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
            ==> whole_pagetable(post, pt_lower, pt_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id) == whole_pagetable(pre, pt_lower, pt_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
}

pub proof fn pagetable_lock_op_preserves_invariant_fields(pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap, changed: RwLockPageTableRoot)
    requires
        post.unchanged_except(&pre, changed),
        post.spec_index(changed).view() == (PageTableHigher { lower_backup: post.spec_index(changed).view().lower_backup, ..pre.spec_index(changed).view() }),
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
            #![trigger process_pagetable_wf(process_map, pre), process_pagetable_wf(process_map, post), pagetable_invariant_fields_unchanged(pre, post, pt_lower)]
            process_pagetable_wf(process_map, pre) && pagetable_invariant_fields_unchanged(pre, post, pt_lower) ==> process_pagetable_wf(process_map, post),
{ reveal(process_pagetable_wf); }

pub proof fn lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall()
    ensures
        forall|pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray|
            #![trigger page_mappings_pagetable_wf(pre, pt_lower, page_array), page_mappings_pagetable_wf(post, pt_lower, page_array)]
            page_mappings_pagetable_wf(pre, pt_lower, page_array) && pagetable_invariant_fields_unchanged(pre, post, pt_lower) ==> page_mappings_pagetable_wf(post, pt_lower, page_array),
{ reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); }

pub proof fn container_process_page_pagetable_wf_preserved_for_pagetable_fields()
    ensures
        forall|container_map: ContainerLockedMap, process_map: ProcessLockedMap, pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray|
            #![trigger container_process_page_pagetable_wf(container_map, process_map, pre, page_array), container_process_page_pagetable_wf(container_map, process_map, post, page_array), pagetable_invariant_fields_unchanged(pre, post, pt_lower)]
            container_process_page_pagetable_wf(container_map, process_map, pre, page_array) && process_pagetable_wf(process_map, pre) && page_mappings_pagetable_wf(pre, pt_lower, page_array)
                && container_owned_pages_wf(container_map, page_array) && pagetable_invariant_fields_unchanged(pre, post, pt_lower)
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
{ reveal(cpu_dirty_map_pagetable_pcid_match); }

pub proof fn lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall()
    ensures
        forall|cpu_tlb: CpuTLB, needflush: PcidNeedFlushArray, cpu_array: CpuLockedArray, pre: PageTableLockedMap, post: PageTableLockedMap, pt_lower: PageTableLowerMap|
            #![trigger cpu_tlb_wf(cpu_tlb, pre, pt_lower, cpu_array, needflush), cpu_tlb_wf(cpu_tlb, post, pt_lower, cpu_array, needflush)]
            cpu_tlb_wf(cpu_tlb, pre, pt_lower, cpu_array, needflush) && pagetable_invariant_fields_unchanged(pre, post, pt_lower) ==> cpu_tlb_wf(cpu_tlb, post, pt_lower, cpu_array, needflush),
{ reveal(cpu_tlb_wf); }
}
