use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {
pub proof fn container_process_page_pagetable_wf_preserved_for_4k_mapping_insert(
    container_map: ContainerLockedMap, process_map: ProcessLockedMap, pre_pagetable_map: PageTableLockedMap, post_pagetable_map: PageTableLockedMap,
    pre_page_array: PageLockedArray, post_page_array: PageLockedArray, pagetable_ptr: RwLockPageTableRoot, pg_ptr: PagePtr, va: VAddr,
)
    requires
        container_process_page_pagetable_wf(container_map, process_map, pre_pagetable_map, pre_page_array),
        container_page_owner_wf(container_map, pre_page_array),
        container_page_owner_wf(container_map, post_page_array),
        process_pagetable_match(process_map, pre_pagetable_map),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        page_ptr_valid(pg_ptr),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_page_array.entries_unchanged_except(&pre_page_array, page_ptr2page_index(pg_ptr)),
        post_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr == pre_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr,
        post_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().is_mapped(),
        post_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings() == if pre_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped4k {
                pre_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().insert((pagetable_ptr, va))
            } else {
                Set::empty().insert((pagetable_ptr, va))
            },
        process_map.dom().contains(post_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr),
        {
            let owner = post_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container;
            let mapping_process = post_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr;
            ||| process_map.spec_index(mapping_process).view_rodata().view().owning_container == owner
            ||| container_map.spec_index(owner).view_ghost().subtree_set.view().contains(process_map.spec_index(mapping_process).view_rodata().view().owning_container)
        },
    ensures
        container_process_page_pagetable_wf(container_map, process_map, post_pagetable_map, post_page_array),
{ reveal(container_page_owner_wf); reveal(container_process_page_pagetable_wf); }

pub proof fn page_pagetable_wf_preserved_for_4k_mapping_insert(
    pre_pagetable_map: PageTableLockedMap, pre_pt_lower: PageTableLowerMap, post_pagetable_map: PageTableLockedMap, post_pt_lower: PageTableLowerMap,
    pre_page_array: PageLockedArray, post_page_array: PageLockedArray, pagetable_ptr: RwLockPageTableRoot, pg_ptr: PagePtr, va: VAddr,
)
    requires
        pagetable_lower_wf(pre_pagetable_map, pre_pt_lower),
        pagetable_lower_wf(post_pagetable_map, post_pt_lower),
        page_array_wf(pre_page_array),
        page_array_wf(post_page_array),
        page_pagetable_wf(pre_pagetable_map, pre_pt_lower, pre_page_array),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        page_ptr_valid(pg_ptr),
        va_4k_valid(va),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_pt_lower == pre_pt_lower.insert(pagetable_ptr, post_pt_lower.spec_index(pagetable_ptr)),
        post_page_array.entries_unchanged_except(&pre_page_array, page_ptr2page_index(pg_ptr)),
        post_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container,
        (pre_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Owned4k
            || pre_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped4k),
        post_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped4k,
        post_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings() == if pre_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped4k {
                pre_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().insert((pagetable_ptr, va))
            } else {
                Set::empty().insert((pagetable_ptr, va))
            },
        whole_pagetable(pre_pagetable_map, pre_pt_lower, pagetable_ptr).mapping_4k().dom().contains(va) == false,
        whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).mapping_4k().dom().contains(va),
        whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).mapping_4k() == whole_pagetable(pre_pagetable_map, pre_pt_lower, pagetable_ptr).mapping_4k().insert(va, whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).mapping_4k().spec_index(va)),
        whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).mapping_4k().spec_index(va).addr == pg_ptr,
        whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).mapping_4k().spec_index(va).owning_container.view() == post_page_array.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container,
        whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).mapping_2m() == whole_pagetable(pre_pagetable_map, pre_pt_lower, pagetable_ptr).mapping_2m(),
        whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).mapping_1g() == whole_pagetable(pre_pagetable_map, pre_pt_lower, pagetable_ptr).mapping_1g(),
        whole_pagetable(pre_pagetable_map, pre_pt_lower, pagetable_ptr).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).kernel_l4_end() == whole_pagetable(pre_pagetable_map, pre_pt_lower, pagetable_ptr).kernel_l4_end(),
        whole_pagetable(pre_pagetable_map, pre_pt_lower, pagetable_ptr).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None,
        whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is Some,
        whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.addr == pg_ptr,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(pre_pagetable_map, pre_pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))
                ==> whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(pre_pagetable_map, pre_pt_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(pre_pagetable_map, pre_pt_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(post_pagetable_map, post_pt_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(pre_pagetable_map, pre_pt_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
    ensures
        page_pagetable_wf(post_pagetable_map, post_pt_lower, post_page_array),
{
    broadcast use {spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip};
    page_ptr_valid_imply_page_index_valid();
    reveal(pagetable_lower_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
}

/// A single non-mapped page may change payload/state without affecting the
/// bidirectional page-table mapping invariant. All mapped pages remain exact
/// because `unchanged_except` frames every other page slot.
pub proof fn page_pagetable_wf_preserved_for_nonmapped_page_change(
    old_pagetable_map: PageTableLockedMap, old_pt_lower: PageTableLowerMap, new_pagetable_map: PageTableLockedMap, new_pt_lower: PageTableLowerMap,
    old_page_array: PageLockedArray, new_page_array: PageLockedArray, changed_page: PageIndex,
)
    requires
        page_pagetable_wf(old_pagetable_map, old_pt_lower, old_page_array),
        pagetable_lower_wf(old_pagetable_map, old_pt_lower),
        new_pagetable_map == old_pagetable_map,
        new_pt_lower == old_pt_lower,
        index_valid(NUM_PAGES, changed_page),
        new_page_array.entries_unchanged_except(&old_page_array, changed_page),
        !old_page_array.spec_index(changed_page).view().view().is_mapped(),
        !new_page_array.spec_index(changed_page).view().view().is_mapped(),
    ensures
        page_pagetable_wf(new_pagetable_map, new_pt_lower, new_page_array),
{ reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf); }

pub proof fn container_process_page_pagetable_wf_preserved_for_page_mapping_fields_eq(container_map: ContainerLockedMap, process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, old_page_array: PageLockedArray, new_page_array: PageLockedArray)
    requires
        container_process_page_pagetable_wf(container_map, process_map, pagetable_map, old_page_array),
        forall|p_i: PageIndex|
            #![trigger new_page_array.spec_index(p_i)]
            index_valid(NUM_PAGES, p_i) && new_page_array.spec_index(p_i).view().view().is_mapped() ==> {
                &&& old_page_array.spec_index(p_i).view().view().is_mapped()
                &&& new_page_array.spec_index(p_i).view().view().mappings() == old_page_array.spec_index(p_i).view().view().mappings()
                &&& new_page_array.spec_index(p_i).view().view().owning_container == old_page_array.spec_index(p_i).view().view().owning_container
            },
    ensures
        container_process_page_pagetable_wf(container_map, process_map, pagetable_map, new_page_array),
{ reveal(container_process_page_pagetable_wf); }
}
