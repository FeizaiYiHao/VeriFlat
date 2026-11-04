use vstd::prelude::*;
use crate::*;
verus! {
    // Proof dependency (confirmed for nonmapped-page changes): pagetable_perms_wf.
    pub open spec fn page_pagetable_wf(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray) -> bool {
        &&& mapped_4k_page_pagetable_wf(pagetable_map, pt_lower, page_array)
        &&& mapped_2m_page_pagetable_wf(pagetable_map, pt_lower, page_array)
        &&& mapped_1g_page_pagetable_wf(pagetable_map, pt_lower, page_array)
    }

    #[verifier::opaque]
    pub open spec fn mapped_4k_page_pagetable_wf(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray) -> bool {
        &&& forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i)]
            index_valid(NUM_PAGES, p_i) && page_array.spec_index(p_i).view().view().state == PageState::Mapped4k ==> forall|pt_ptr:RwLockPageTableRoot, va: VAddr|
                #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
                page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va)) ==> {
                    &&& pagetable_map.dom().contains(pt_ptr)
                    &&& va_4k_valid(va)
                    &&& whole_pagetable(pagetable_map, pt_lower, pt_ptr).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is Some
                    &&& whole_pagetable(pagetable_map, pt_lower, pt_ptr).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.addr == page_index2page_ptr(p_i)
                }
        &&& forall|pt_ptr:RwLockPageTableRoot|
            #![trigger pagetable_map.dom().contains(pt_ptr)]
            pagetable_map.dom().contains(pt_ptr) ==> forall|va: VAddr|
                #![trigger whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_4k().contains_key(va)]
                #![trigger whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_4k().spec_index(va)]
                whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_4k().contains_key(va)
                    ==> page_array.spec_index(page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_4k().spec_index(va).addr)).view().view().state == PageState::Mapped4k
                    && page_array.spec_index(page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_4k().spec_index(va).addr)).view().view().mappings().contains((pt_ptr, va))
                    && whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_4k().spec_index(va).owning_container.view() == page_array.spec_index(page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_4k().spec_index(va).addr)).view().view().owning_container
        &&& forall|pt_ptr:RwLockPageTableRoot|
            #![trigger pagetable_map.dom().contains(pt_ptr)]
            pagetable_map.dom().contains(pt_ptr) ==> forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger whole_pagetable(pagetable_map, pt_lower, pt_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                whole_pagetable(pagetable_map, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    && whole_pagetable(pagetable_map, pt_lower, pt_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) is Some ==> {
                    let p_i = page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.addr);
                    &&& index_valid(NUM_PAGES, p_i)
                    &&& page_array.spec_index(p_i).view().view().state == PageState::Mapped4k
                    &&& page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, spec_index2va((l4i, l3i, l2i, l1i))))
                }
    }

    pub proof fn mapped_4k_page_pagetable_wf_pagetable_at(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray, pt_ptr: RwLockPageTableRoot, va: VAddr)
        requires
            mapped_4k_page_pagetable_wf(pagetable_map, pt_lower, page_array),
        ensures
            pagetable_map.dom().contains(pt_ptr) && whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_4k().contains_key(va) ==> ({
                let p_i = page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_4k().spec_index(va).addr);
                &&& page_array.spec_index(p_i).view().view().state == PageState::Mapped4k
                &&& page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))
                &&& whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_4k().spec_index(va).owning_container.view() == page_array.spec_index(p_i).view().view().owning_container
            }),
    { reveal(mapped_4k_page_pagetable_wf); }

    /// A `(pt_ptr, va)` record on the `Mapped4k` page `p_i` names a held 4K leaf of `pt_ptr` that points back at the page.
    pub proof fn mapped_4k_page_pagetable_wf_page_at(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray, p_i: PageIndex, pt_ptr: RwLockPageTableRoot, va: VAddr)
        requires
            mapped_4k_page_pagetable_wf(pagetable_map, pt_lower, page_array),
            index_valid(NUM_PAGES, p_i),
            page_array.spec_index(p_i).view().view().state == PageState::Mapped4k,
        ensures
            page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va)) ==> {
                &&& pagetable_map.dom().contains(pt_ptr)
                &&& va_4k_valid(va)
                &&& whole_pagetable(pagetable_map, pt_lower, pt_ptr).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is Some
                &&& whole_pagetable(pagetable_map, pt_lower, pt_ptr).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.addr == page_index2page_ptr(p_i)
            },
    { reveal(mapped_4k_page_pagetable_wf); }

    /// A held user 4K leaf of `pt_ptr`, present or as a placeholder, points at a valid `Mapped4k` page that records `(pt_ptr, va)`.
    pub proof fn mapped_4k_page_pagetable_wf_held_leaf_at(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray, pt_ptr: RwLockPageTableRoot,
        l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index)
        requires
            mapped_4k_page_pagetable_wf(pagetable_map, pt_lower, page_array),
        ensures
            pagetable_map.dom().contains(pt_ptr) && whole_pagetable(pagetable_map, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                && whole_pagetable(pagetable_map, pt_lower, pt_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) is Some ==> ({
                let p_i = page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.addr);
                &&& index_valid(NUM_PAGES, p_i)
                &&& page_array.spec_index(p_i).view().view().state == PageState::Mapped4k
                &&& page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, spec_index2va((l4i, l3i, l2i, l1i))))
            }),
    { reveal(mapped_4k_page_pagetable_wf); }

    #[verifier::opaque]
    pub open spec fn mapped_2m_page_pagetable_wf(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray) -> bool {
        &&& forall|p_i:PageIndex, pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
            index_valid(NUM_PAGES, p_i) && page_array.spec_index(p_i).view().view().state == PageState::Mapped2m && page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va)) ==> {
                &&& pagetable_map.dom().contains(pt_ptr)
                &&& va_2m_valid(va)
                &&& whole_pagetable(pagetable_map, pt_lower, pt_ptr).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
                &&& whole_pagetable(pagetable_map, pt_lower, pt_ptr).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.addr == page_index2page_ptr(p_i)
            }
        &&& forall|pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_2m().contains_key(va)]
            pagetable_map.dom().contains(pt_ptr) && whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_2m().contains_key(va)
                ==> page_array.spec_index(page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_2m().spec_index(va).addr)).view().view().state == PageState::Mapped2m
                && page_array.spec_index(page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_2m().spec_index(va).addr)).view().view().mappings().contains((pt_ptr, va))
                && whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_2m().spec_index(va).owning_container.view() == page_array.spec_index(page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_2m().spec_index(va).addr)).view().view().owning_container
    }

    #[verifier::opaque]
    pub open spec fn mapped_1g_page_pagetable_wf(pagetable_map: PageTableLockedMap, pt_lower: PageTableLowerMap, page_array: PageLockedArray) -> bool {
        &&& forall|p_i:PageIndex, pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
            index_valid(NUM_PAGES, p_i) && page_array.spec_index(p_i).view().view().state == PageState::Mapped1g && page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))
                ==> pagetable_map.dom().contains(pt_ptr) && whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_1g().contains_key(va) && whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_1g().spec_index(va).addr == page_index2page_ptr(p_i)
        &&& forall|pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_1g().contains_key(va)]
            pagetable_map.dom().contains(pt_ptr) && whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_1g().contains_key(va)
                ==> page_array.spec_index(page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_1g().spec_index(va).addr)).view().view().state == PageState::Mapped1g
                && page_array.spec_index(page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_1g().spec_index(va).addr)).view().view().mappings().contains((pt_ptr, va))
                && whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_1g().spec_index(va).owning_container.view() == page_array.spec_index(page_ptr2page_index(whole_pagetable(pagetable_map, pt_lower, pt_ptr).mapping_1g().spec_index(va).addr)).view().view().owning_container
    }

    // Proof dependencies (confirmed for global-pool page removal): container_page_owner_wf,
    // mapped_4k_page_pagetable_wf, mapped_2m_page_pagetable_wf, mapped_1g_page_pagetable_wf.
    #[verifier::opaque]
    pub open spec fn container_process_page_pagetable_wf(container_map: ContainerLockedMap, process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, page_array: PageLockedArray) -> bool {
        &&& forall|p_i:PageIndex, pt_ptr:RwLockPageTableRoot, va: VAddr|
            #![trigger page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va))]
            index_valid(NUM_PAGES, p_i) && page_array.spec_index(p_i).view().view().is_mapped() && page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, va)) ==> {
                let proc_ptr = pagetable_map.spec_index(pt_ptr).view().proc_ptr;
                let page_owner = page_array.spec_index(p_i).view().view().owning_container;
                &&& pagetable_map.dom().contains(pt_ptr)
                &&& process_map.dom().contains(proc_ptr)
                &&& container_map.dom().contains(page_owner)
                &&& {
                    ||| process_map.spec_index(proc_ptr).view_rodata().view().owning_container == page_owner
                    ||| container_map.spec_index(page_owner).view_ghost().subtree_set.view().contains(process_map.spec_index(proc_ptr).view_rodata().view().owning_container)
                }
            }
    }
}
