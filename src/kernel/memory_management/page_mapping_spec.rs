use vstd::prelude::*;
use crate::*;
verus! {
/// Mapped 4K, 2M, and 1G pages and the leaves of the CPU page tables agree.
// Proof dependency (confirmed for nonmapped-page changes): pagetable_perms_wf.
pub open spec fn page_mappings_pagetable_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray) -> bool {
    &&& mapped_4k_page_pagetable_wf(pt_mp, pt_lower, pg_arr)
    &&& mapped_2m_page_pagetable_wf(pt_mp, pt_lower, pg_arr)
    &&& mapped_1g_page_pagetable_wf(pt_mp, pt_lower, pg_arr)
}

/// Mapped4k pages and the 4K L1 entries of the CPU page tables agree in both directions.
#[verifier::opaque]
pub open spec fn mapped_4k_page_pagetable_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray) -> bool {
    // A Mapped4k page's mappings name 4K L1 entries with the kernel_present bit set that point back at it.
    &&& forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i)]
        index_valid(NUM_PAGES, p_i) && pg_arr.spec_index(p_i).view().view().state == PageState::Mapped4k
            ==>
            forall|pt: RwLockPageTableRoot, va: VAddr|
                #![trigger pg_arr.spec_index(p_i).view().view().mappings().contains((pt, va))]
                pg_arr.spec_index(p_i).view().view().mappings().contains((pt, va)) ==> {
                    let leaf = whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
                    &&& pt_mp.dom().contains(pt)
                    &&& va_4k_valid(va)
                    &&& leaf is Some
                    &&& leaf->0.addr == page_index2page_ptr(p_i)
                }
    // Every present 4K mapping of a table points at a Mapped4k page that lists it and shares its container.
    &&& forall|pt: RwLockPageTableRoot|
        #![trigger pt_mp.dom().contains(pt)]
        pt_mp.dom().contains(pt)
            ==>
            forall|va: VAddr|
                #![trigger whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().contains_key(va)]
                #![trigger whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va)]
                whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().contains_key(va) ==> {
                    let entry = whole_pagetable(pt_mp, pt_lower, pt).mapping_4k().spec_index(va);
                    let page = pg_arr.spec_index(page_ptr2page_index(entry.addr)).view().view();
                    &&& page.state == PageState::Mapped4k
                    &&& page.mappings().contains((pt, va))
                    &&& entry.owning_container.view() == page.owning_container
                }
    // Every user 4K L1 entry with the kernel_present bit set points at a Mapped4k page that lists it.
    &&& forall|pt: RwLockPageTableRoot|
        #![trigger pt_mp.dom().contains(pt)]
        pt_mp.dom().contains(pt)
            ==>
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                whole_pagetable(pt_mp, pt_lower, pt).kernel_l4_end() <= l4i
                    && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    && pei_valid(l1i)
                    && whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i) is Some
                    ==> {
                        let pg_idx = page_ptr2page_index(whole_pagetable(pt_mp, pt_lower, pt).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.addr);
                        &&& index_valid(NUM_PAGES, pg_idx)
                        &&& pg_arr.spec_index(pg_idx).view().view().state == PageState::Mapped4k
                        &&& pg_arr.spec_index(pg_idx).view().view().mappings().contains((pt, spec_index2va((l4i, l3i, l2i, l1i))))
                    }
}

pub proof fn mapped_4k_page_pagetable_wf_pagetable_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray, pt_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        mapped_4k_page_pagetable_wf(pt_mp, pt_lower, pg_arr),
    ensures
        pt_mp.dom().contains(pt_ptr) && whole_pagetable(pt_mp, pt_lower, pt_ptr).mapping_4k().contains_key(va) ==> ({
            let pg_idx = page_ptr2page_index(whole_pagetable(pt_mp, pt_lower, pt_ptr).mapping_4k().spec_index(va).addr);
            &&& pg_arr.spec_index(pg_idx).view().view().state == PageState::Mapped4k
            &&& pg_arr.spec_index(pg_idx).view().view().mappings().contains((pt_ptr, va))
            &&& whole_pagetable(pt_mp, pt_lower, pt_ptr).mapping_4k().spec_index(va).owning_container.view() == pg_arr.spec_index(pg_idx).view().view().owning_container
        }),
{ reveal(mapped_4k_page_pagetable_wf); }

/// A mapping `(pt_ptr, va)` in the mappings of the `Mapped4k` page `pg_idx` names a 4K L1 entry of `pt_ptr` with the
/// kernel_present bit set that points back at the page.
pub proof fn mapped_4k_page_pagetable_wf_page_at(
    pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray, pg_idx: PageIndex, pt_ptr: RwLockPageTableRoot, va: VAddr,
)
    requires
        mapped_4k_page_pagetable_wf(pt_mp, pt_lower, pg_arr),
        index_valid(NUM_PAGES, pg_idx),
        pg_arr.spec_index(pg_idx).view().view().state == PageState::Mapped4k,
    ensures
        pg_arr.spec_index(pg_idx).view().view().mappings().contains((pt_ptr, va)) ==> {
            let leaf = whole_pagetable(pt_mp, pt_lower, pt_ptr).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
            &&& pt_mp.dom().contains(pt_ptr)
            &&& va_4k_valid(va)
            &&& leaf is Some
            &&& leaf->0.addr == page_index2page_ptr(pg_idx)
        },
{ reveal(mapped_4k_page_pagetable_wf); }

/// A user 4K L1 entry of `pt_ptr` with the kernel_present bit set (present bit set or clear) points at a valid `Mapped4k`
/// page that lists `(pt_ptr, va)` in its mappings.
pub proof fn mapped_4k_page_pagetable_wf_held_leaf_at(
    pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray, pt_ptr: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index,
    l1i: L1Index,
)
    requires
        mapped_4k_page_pagetable_wf(pt_mp, pt_lower, pg_arr),
    ensures
        pt_mp.dom().contains(pt_ptr)
            && whole_pagetable(pt_mp, pt_lower, pt_ptr).kernel_l4_end() <= l4i
            && pei_valid(l4i)
            && pei_valid(l3i)
            && pei_valid(l2i)
            && pei_valid(l1i)
            && whole_pagetable(pt_mp, pt_lower, pt_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) is Some
            ==> ({
                let pg_idx = page_ptr2page_index(whole_pagetable(pt_mp, pt_lower, pt_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)->0.addr);
                &&& index_valid(NUM_PAGES, pg_idx)
                &&& pg_arr.spec_index(pg_idx).view().view().state == PageState::Mapped4k
                &&& pg_arr.spec_index(pg_idx).view().view().mappings().contains((pt_ptr, spec_index2va((l4i, l3i, l2i, l1i))))
            }),
{ reveal(mapped_4k_page_pagetable_wf); }

/// Mapped2m pages and the 2M L2 entries of the CPU page tables agree in both directions.
#[verifier::opaque]
pub open spec fn mapped_2m_page_pagetable_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray) -> bool {
    // A Mapped2m page's mappings name 2M L2 entries with the kernel_present bit set that point back at it.
    &&& forall|p_i: PageIndex, pt: RwLockPageTableRoot, va: VAddr|
        #![trigger pg_arr.spec_index(p_i).view().view().mappings().contains((pt, va))]
        index_valid(NUM_PAGES, p_i)
            && pg_arr.spec_index(p_i).view().view().state == PageState::Mapped2m
            && pg_arr.spec_index(p_i).view().view().mappings().contains((pt, va))
            ==> {
                let leaf = whole_pagetable(pt_mp, pt_lower, pt).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
                &&& pt_mp.dom().contains(pt)
                &&& va_2m_valid(va)
                &&& leaf is Some
                &&& leaf->0.addr == page_index2page_ptr(p_i)
            }
    // Every present 2M mapping of a table points at a Mapped2m page that lists it and shares its container.
    &&& forall|pt: RwLockPageTableRoot, va: VAddr|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().contains_key(va)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().contains_key(va) ==> {
            let entry = whole_pagetable(pt_mp, pt_lower, pt).mapping_2m().spec_index(va);
            let page = pg_arr.spec_index(page_ptr2page_index(entry.addr)).view().view();
            &&& page.state == PageState::Mapped2m
            &&& page.mappings().contains((pt, va))
            &&& entry.owning_container.view() == page.owning_container
        }
}

/// Mapped1g pages and the 1G mappings of the CPU page tables agree in both directions.
#[verifier::opaque]
pub open spec fn mapped_1g_page_pagetable_wf(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray) -> bool {
    // A Mapped1g page's mappings name 1G mappings of their tables that point back at it.
    &&& forall|p_i: PageIndex, pt: RwLockPageTableRoot, va: VAddr|
        #![trigger pg_arr.spec_index(p_i).view().view().mappings().contains((pt, va))]
        index_valid(NUM_PAGES, p_i)
            && pg_arr.spec_index(p_i).view().view().state == PageState::Mapped1g
            && pg_arr.spec_index(p_i).view().view().mappings().contains((pt, va))
            ==> {
                &&& pt_mp.dom().contains(pt)
                &&& whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().contains_key(va)
                &&& whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().spec_index(va).addr == page_index2page_ptr(p_i)
            }
    // Every present 1G mapping of a table points at a Mapped1g page that lists it and shares its container.
    &&& forall|pt: RwLockPageTableRoot, va: VAddr|
        #![trigger whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().contains_key(va)]
        pt_mp.dom().contains(pt) && whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().contains_key(va) ==> {
            let entry = whole_pagetable(pt_mp, pt_lower, pt).mapping_1g().spec_index(va);
            let page = pg_arr.spec_index(page_ptr2page_index(entry.addr)).view().view();
            &&& page.state == PageState::Mapped1g
            &&& page.mappings().contains((pt, va))
            &&& entry.owning_container.view() == page.owning_container
        }
}

/// A mapped page's owner is its table's process's container or an ancestor of it.
// Proof dependencies (confirmed for global-pool page removal): container_owned_pages_wf,
// mapped_4k_page_pagetable_wf, mapped_2m_page_pagetable_wf, mapped_1g_page_pagetable_wf.
#[verifier::opaque]
pub open spec fn container_process_page_pagetable_wf(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap, pg_arr: PageLockedArray) -> bool {
    &&& forall|p_i: PageIndex, pt: RwLockPageTableRoot, va: VAddr|
        #![trigger pg_arr.spec_index(p_i).view().view().mappings().contains((pt, va))]
        index_valid(NUM_PAGES, p_i)
            && pg_arr.spec_index(p_i).view().view().is_mapped()
            && pg_arr.spec_index(p_i).view().view().mappings().contains((pt, va))
            ==> {
                let prc_ptr = pt_mp.spec_index(pt).view().proc_ptr;
                let page_owner = pg_arr.spec_index(p_i).view().view().owning_container;
                &&& pt_mp.dom().contains(pt)
                &&& prc_mp.dom().contains(prc_ptr)
                &&& ctn_mp.dom().contains(page_owner)
                &&& {
                    ||| prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == page_owner
                    ||| ctn_mp.spec_index(page_owner).view_ghost().subtree_set.view().contains(prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container)
                }
            }
}

/// The owner of the mapped page `pg_idx` whose mappings contain `(pt_ptr, va)` is the container of that table's process or
/// one of its ancestors.
pub proof fn container_process_page_pagetable_wf_at(
    ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap, pg_arr: PageLockedArray, pg_idx: PageIndex, pt_ptr: RwLockPageTableRoot,
    va: VAddr,
)
    requires
        container_process_page_pagetable_wf(ctn_mp, prc_mp, pt_mp, pg_arr),
        index_valid(NUM_PAGES, pg_idx),
        pg_arr.spec_index(pg_idx).view().view().is_mapped(),
        pg_arr.spec_index(pg_idx).view().view().mappings().contains((pt_ptr, va)),
    ensures
        ({
            let prc_ptr = pt_mp.spec_index(pt_ptr).view().proc_ptr;
            let page_owner = pg_arr.spec_index(pg_idx).view().view().owning_container;
            &&& pt_mp.dom().contains(pt_ptr)
            &&& prc_mp.dom().contains(prc_ptr)
            &&& ctn_mp.dom().contains(page_owner)
            &&& {
                ||| prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == page_owner
                ||| ctn_mp.spec_index(page_owner).view_ghost().subtree_set.view().contains(prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container)
            }
        }),
{ reveal(container_process_page_pagetable_wf); }
}
