use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

pub proof fn container_process_page_pagetable_wf_preserved_for_4k_mapping_insert(
    container_map: ContainerLockedMap,
    process_map: ProcessLockedMap,
    pre_pagetable_map: PageTableLockedMap,
    post_pagetable_map: PageTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    pagetable_ptr: RwLockPageTableRoot,
    page_ptr: PagePtr,
    va: VAddr,
)
    requires
        container_process_page_pagetable_wf(
            container_map,
            process_map,
            pre_pagetable_map,
            pre_page_array,
        ),
        page_pagetable_wf(pre_pagetable_map, pre_page_array),
        page_pagetable_wf(post_pagetable_map, post_page_array),
        container_page_owner_wf(container_map, pre_page_array),
        container_page_owner_wf(container_map, post_page_array),
        process_pagetable_match(process_map, pre_pagetable_map),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        page_ptr_valid(page_ptr),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_page_array.entries_unchanged_except(&pre_page_array, page_ptr2page_index(page_ptr)),
        post_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr
            == pre_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr,
        post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().is_mapped(),
        post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings()
            == if pre_page_array.spec_index(page_ptr2page_index(page_ptr))
                .view().view().state is Mapped4k {
                pre_page_array.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().mappings().insert((pagetable_ptr, va))
            } else {
                Set::empty().insert((pagetable_ptr, va))
            },
        process_map.dom().contains(post_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr),
        {
            let owner = post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container;
            let mapping_process = post_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr;
            ||| process_map.spec_index(mapping_process).view_rodata().view().owning_container == owner
            ||| container_map.spec_index(owner).view().subtree_set.view().contains(
                process_map.spec_index(mapping_process).view_rodata().view().owning_container,
            )
        },
    ensures
        container_process_page_pagetable_wf(
            container_map,
            process_map,
            post_pagetable_map,
            post_page_array,
        ),
{
    reveal(mapped_4k_page_pagetable_wf);
    reveal(mapped_2m_page_pagetable_wf);
    reveal(mapped_1g_page_pagetable_wf);
    reveal(container_page_owner_wf);
    reveal(process_pagetable_match);
    assert forall|pt_ptr: RwLockPageTableRoot|
        #![trigger post_pagetable_map.spec_index(pt_ptr).view().proc_ptr]
        post_pagetable_map.dom().contains(pt_ptr)
        implies post_pagetable_map.spec_index(pt_ptr).view().proc_ptr
            == pre_pagetable_map.spec_index(pt_ptr).view().proc_ptr by {
        if pt_ptr == pagetable_ptr {
        }
    };
    reveal(container_process_page_pagetable_wf);
    assert forall|p_i: PageIndex, pt_ptr: RwLockPageTableRoot, mapped_va: VAddr|
        #![trigger post_page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, mapped_va))]
        index_valid(NUM_PAGES, p_i)
        && post_page_array.spec_index(p_i).view().view().is_mapped()
        && post_page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, mapped_va))
        implies {
            let owner = post_page_array.spec_index(p_i).view().view().owning_container;
            let mapping_process = post_pagetable_map.spec_index(pt_ptr).view().proc_ptr;
            ||| process_map.spec_index(mapping_process).view_rodata().view().owning_container == owner
            ||| container_map.spec_index(owner).view().subtree_set.view().contains(
                process_map.spec_index(mapping_process).view_rodata().view().owning_container,
            )
        } by {
        if p_i == page_ptr2page_index(page_ptr) {
        } else if pt_ptr == pagetable_ptr {
        }
    };
}

pub proof fn page_pagetable_wf_preserved_for_4k_mapping_insert(
    pre_pagetable_map: PageTableLockedMap,
    post_pagetable_map: PageTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    pagetable_ptr: RwLockPageTableRoot,
    page_ptr: PagePtr,
    va: VAddr,
)
    requires
        pagetable_perms_wf(pre_pagetable_map),
        pagetable_perms_wf(post_pagetable_map),
        page_array_wf(pre_page_array),
        page_array_wf(post_page_array),
        page_pagetable_wf(pre_pagetable_map, pre_page_array),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        page_ptr_valid(page_ptr),
        va_4k_valid(va),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_page_array.entries_unchanged_except(&pre_page_array, page_ptr2page_index(page_ptr)),
        post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container
            == pre_page_array.spec_index(page_ptr2page_index(page_ptr))
                .view().view().owning_container,
        (pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k
            || pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Mapped4k),
        post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Mapped4k,
        post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings()
            == if pre_page_array.spec_index(page_ptr2page_index(page_ptr))
                .view().view().state is Mapped4k {
                pre_page_array.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().mappings().insert((pagetable_ptr, va))
            } else {
                Set::empty().insert((pagetable_ptr, va))
            },
        pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va)
            == false,
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k().insert(
                va,
                post_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va),
            ),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va).addr
            == page_ptr,
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                .spec_index(va).owning_container@
            == post_page_array.spec_index(page_ptr2page_index(page_ptr))
                .view().view().owning_container,
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
    ensures
        page_pagetable_wf(post_pagetable_map, post_page_array),
{
    reveal(pagetable_perms_wf);
    reveal(page_array_wf);
    reveal(mapped_4k_page_pagetable_wf);
    assert forall|p_i: PageIndex, pt_ptr: RwLockPageTableRoot, mapped_va: VAddr|
        #![trigger post_page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, mapped_va))]
        index_valid(NUM_PAGES, p_i)
        && post_page_array.spec_index(p_i).view().view().state is Mapped4k
        && post_page_array.spec_index(p_i).view().view().mappings().contains((pt_ptr, mapped_va))
        implies
            post_pagetable_map.dom().contains(pt_ptr)
            && post_pagetable_map.spec_index(pt_ptr).view().mapping_4k().dom().contains(mapped_va)
            && post_pagetable_map.spec_index(pt_ptr).view().mapping_4k().spec_index(mapped_va).addr
                == page_index2page_ptr(p_i) by {
        page_ptr_roundtrip();
        if p_i == page_ptr2page_index(page_ptr) {
        } else if pt_ptr == pagetable_ptr {
        }
    };
    assert forall|pt_ptr: RwLockPageTableRoot, mapped_va: VAddr|
        #![trigger post_pagetable_map.spec_index(pt_ptr).view().mapping_4k().dom().contains(mapped_va)]
        post_pagetable_map.dom().contains(pt_ptr)
        && post_pagetable_map.spec_index(pt_ptr).view().mapping_4k().dom().contains(mapped_va)
        implies {
            let mapped_page = page_ptr2page_index(
                post_pagetable_map.spec_index(pt_ptr).view().mapping_4k().spec_index(mapped_va).addr,
            );
            &&& index_valid(NUM_PAGES, mapped_page)
            &&& post_page_array.spec_index(mapped_page).view().view().state is Mapped4k
            &&& post_page_array.spec_index(mapped_page).view().view().mappings().contains((pt_ptr, mapped_va))
            &&& post_pagetable_map.spec_index(pt_ptr).view().mapping_4k()
                    .spec_index(mapped_va).owning_container@
                == post_page_array.spec_index(mapped_page).view().view().owning_container
        } by {
        page_ptr_valid_imply_page_index_valid();
        if pt_ptr == pagetable_ptr && mapped_va == va {
        } else if page_ptr2page_index(
            post_pagetable_map.spec_index(pt_ptr).view().mapping_4k().spec_index(mapped_va).addr,
        ) == page_ptr2page_index(page_ptr) {
        }
    };
    assert(mapped_4k_page_pagetable_wf(post_pagetable_map, post_page_array)) by {
        reveal(mapped_4k_page_pagetable_wf);
    };
    assert forall|p_i: PageIndex|
        #![trigger post_page_array.spec_index(p_i).view().view().state]
        index_valid(NUM_PAGES, p_i)
        && ((pre_page_array.spec_index(p_i).view().view().state is Mapped2m)
            || (post_page_array.spec_index(p_i).view().view().state is Mapped2m))
        implies post_page_array.spec_index(p_i) === pre_page_array.spec_index(p_i) by {
        if p_i == page_ptr2page_index(page_ptr) {
        }
    };
    assert forall|pt_ptr: RwLockPageTableRoot|
        #![trigger post_pagetable_map.spec_index(pt_ptr).view().mapping_2m()]
        post_pagetable_map.dom().contains(pt_ptr)
        implies post_pagetable_map.spec_index(pt_ptr).view().mapping_2m()
            == pre_pagetable_map.spec_index(pt_ptr).view().mapping_2m() by {
        if pt_ptr == pagetable_ptr {
        }
    };
    assert(mapped_2m_page_pagetable_wf(post_pagetable_map, post_page_array)) by {
        reveal(mapped_2m_page_pagetable_wf);
    };
    assert forall|p_i: PageIndex|
        #![trigger post_page_array.spec_index(p_i).view().view().state]
        index_valid(NUM_PAGES, p_i)
        && ((pre_page_array.spec_index(p_i).view().view().state is Mapped1g)
            || (post_page_array.spec_index(p_i).view().view().state is Mapped1g))
        implies post_page_array.spec_index(p_i) === pre_page_array.spec_index(p_i) by {
        if p_i == page_ptr2page_index(page_ptr) {
        }
    };
    assert forall|pt_ptr: RwLockPageTableRoot|
        #![trigger post_pagetable_map.spec_index(pt_ptr).view().mapping_1g()]
        post_pagetable_map.dom().contains(pt_ptr)
        implies post_pagetable_map.spec_index(pt_ptr).view().mapping_1g()
            == pre_pagetable_map.spec_index(pt_ptr).view().mapping_1g() by {
        if pt_ptr == pagetable_ptr {
        }
    };
    assert(mapped_1g_page_pagetable_wf(post_pagetable_map, post_page_array)) by {
        reveal(mapped_1g_page_pagetable_wf);
    };
}

/// A single non-mapped page may change payload/state without affecting the
/// bidirectional page-table mapping invariant. All mapped pages remain exact
/// because `unchanged_except` frames every other page slot.
pub proof fn page_pagetable_wf_preserved_for_nonmapped_page_change(
    old_pagetable_map: PageTableLockedMap,
    new_pagetable_map: PageTableLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
    changed_page: PageIndex,
)
    requires
        page_pagetable_wf(old_pagetable_map, old_page_array),
        pagetable_perms_wf(old_pagetable_map),
        new_pagetable_map == old_pagetable_map,
        index_valid(NUM_PAGES, changed_page),
        new_page_array.entries_unchanged_except(&old_page_array, changed_page),
        !old_page_array.spec_index(changed_page).view().view().is_mapped(),
        !new_page_array.spec_index(changed_page).view().view().is_mapped(),
    ensures
        page_pagetable_wf(new_pagetable_map, new_page_array),
{
    assert(page_pagetable_wf(new_pagetable_map, new_page_array)) by {
 
        reveal(mapped_4k_page_pagetable_wf);
        reveal(mapped_2m_page_pagetable_wf);
        reveal(mapped_1g_page_pagetable_wf);
        reveal(pagetable_perms_wf);
        page_ptr_valid_imply_page_index_valid();
        assert(mapped_4k_page_pagetable_wf(new_pagetable_map, new_page_array));      
        assert(mapped_2m_page_pagetable_wf(new_pagetable_map, new_page_array));        
        assert(mapped_1g_page_pagetable_wf(new_pagetable_map, new_page_array));
    };
}

/// A lock-state-only change preserves the mapping invariant: every non-target
/// slot is unchanged and every payload is unchanged.
pub proof fn page_pagetable_wf_preserved_for_page_lock_change(
    old_pagetable_map: PageTableLockedMap,
    new_pagetable_map: PageTableLockedMap,
    old_page_array: PageLockedArray,
    new_page_array: PageLockedArray,
    changed_page: PageIndex,
)
    requires
        page_pagetable_wf(old_pagetable_map, old_page_array),
        pagetable_perms_wf(old_pagetable_map),
        new_pagetable_map == old_pagetable_map,
        index_valid(NUM_PAGES, changed_page),
        new_page_array.unchanged_except(&old_page_array, changed_page),
    ensures
        page_pagetable_wf(new_pagetable_map, new_page_array),
{
    assert(page_pagetable_wf(new_pagetable_map, new_page_array)) by {
 
        reveal(mapped_4k_page_pagetable_wf);
        reveal(mapped_2m_page_pagetable_wf);
        reveal(mapped_1g_page_pagetable_wf);
        reveal(pagetable_perms_wf);
        page_ptr_valid_imply_page_index_valid();
    };
}

}
