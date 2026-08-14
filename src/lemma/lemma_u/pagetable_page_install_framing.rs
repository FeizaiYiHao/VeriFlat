use vstd::prelude::*;
use crate::*;

verus! {

/// Installing one freshly initialized page-table page grows exactly one
/// page-table closure and retags the backing `Page` with that closure's root.
/// This is the structural counterpart of the nonstructural mmap framing lemma.
pub proof fn pagetable_pages_wf_preserved_for_page_table_page_insert(
    pre_pagetable_map: PageTableLockedMap,
    post_pagetable_map: PageTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    pagetable_ptr: RwLockPageTableRoot,
    page_ptr: PagePtr,
)
    requires
        pagetable_pages_wf(pre_pagetable_map, pre_page_array),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        page_ptr_valid(page_ptr),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_pagetable_map.spec_index(pagetable_ptr).view().page_closure()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().page_closure()
                .insert(page_ptr),
        post_page_array.unchanged_except(
            &pre_page_array,
            page_ptr2page_index(page_ptr),
        ),
        pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
            is Owned4k,
        post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
            == (PageState::Allocated4k {
                state: Allocated4KPageState::PageTable {
                    pagetable_root: pagetable_ptr,
                },
            }),
    ensures
        pagetable_pages_wf(post_pagetable_map, post_page_array),
{
    assert(pagetable_pages_wf(post_pagetable_map, post_page_array)) by {
        reveal(pagetable_pages_wf);
        assert(page_index2page_ptr(page_ptr2page_index(page_ptr)) == page_ptr) by {
            page_ptr_roundtrip();
        };
        assert forall|page_index: PageIndex|
            #![trigger post_pagetable_map.dom().contains(page_index2page_ptr(page_index))]
            page_index_wf(page_index)
            && (post_page_array.spec_index(page_index).view().view().state matches
                PageState::Allocated4k {
                    state: Allocated4KPageState::AsPageTableRoot,
                })
        implies post_pagetable_map.dom().contains(page_index2page_ptr(page_index)) by {
            if page_index == page_ptr2page_index(page_ptr) {
            }
        };
        assert forall|page_index: PageIndex|
            #![trigger post_pagetable_map.dom().contains(
                post_page_array.spec_index(page_index).view().view().state
                    ->Allocated4k_state->PageTable_pagetable_root)]
            #![trigger post_pagetable_map.spec_index(
                post_page_array.spec_index(page_index).view().view().state
                    ->Allocated4k_state->PageTable_pagetable_root)
                .view().page_closure().contains(page_index2page_ptr(page_index))]
            page_index_wf(page_index)
            && (post_page_array.spec_index(page_index).view().view().state matches
                PageState::Allocated4k {
                    state: Allocated4KPageState::PageTable { pagetable_root },
                })
        implies {
            let root = post_page_array.spec_index(page_index).view().view().state
                ->Allocated4k_state->PageTable_pagetable_root;
            &&& post_pagetable_map.dom().contains(root)
            &&& post_pagetable_map.spec_index(root).view().page_closure()
                .contains(page_index2page_ptr(page_index))
        } by {
            if page_index == page_ptr2page_index(page_ptr) {
            } else {
                let root = post_page_array.spec_index(page_index).view().view().state
                    ->Allocated4k_state->PageTable_pagetable_root;
                if root == pagetable_ptr {
                }
            }
        };
        assert forall|pt_ptr: RwLockPageTableRoot|
            #![trigger post_pagetable_map.dom().contains(pt_ptr)]
            post_pagetable_map.dom().contains(pt_ptr)
        implies {
            let root_page_index = page_ptr2page_index(pt_ptr);
            &&& page_ptr_valid(pt_ptr)
            &&& post_page_array.spec_index(root_page_index).view().view().state
                is Allocated4k
            &&& post_page_array.spec_index(root_page_index).view().view().state
                ->Allocated4k_state is AsPageTableRoot
        } by {
            if page_ptr2page_index(pt_ptr) == page_ptr2page_index(page_ptr) {
                assert(page_index2page_ptr(page_ptr2page_index(pt_ptr)) == pt_ptr) by {
                    page_ptr_roundtrip();
                };
            }
        };
        assert forall|pt_ptr: RwLockPageTableRoot, table_page: PagePtr|
            #![trigger post_pagetable_map.spec_index(pt_ptr).view()
                .page_closure().contains(table_page)]
            post_pagetable_map.dom().contains(pt_ptr)
            && post_pagetable_map.spec_index(pt_ptr).view().page_closure()
                .contains(table_page)
        implies {
            &&& page_ptr_valid(table_page)
            &&& post_page_array.spec_index(page_ptr2page_index(table_page)).view()
                .view().state is Allocated4k
            &&& post_page_array.spec_index(page_ptr2page_index(table_page)).view()
                .view().state->Allocated4k_state is PageTable
            &&& post_page_array.spec_index(page_ptr2page_index(table_page)).view()
                .view().state->Allocated4k_state->PageTable_pagetable_root == pt_ptr
        } by {
            if pt_ptr == pagetable_ptr {
                if table_page == page_ptr {
                }
            }
            if page_ptr2page_index(table_page) == page_ptr2page_index(page_ptr) {
                assert(page_index2page_ptr(page_ptr2page_index(table_page)) == table_page) by {
                    page_ptr_roundtrip();
                };
            }
        };
    };
}

/// A page-table structure-only change leaves all abstract mappings untouched;
/// changing one nonmapped backing page therefore preserves the page/mapping
/// bidirectional invariant.
pub proof fn page_pagetable_wf_preserved_for_page_table_page_insert(
    pre_pagetable_map: PageTableLockedMap,
    post_pagetable_map: PageTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    pagetable_ptr: RwLockPageTableRoot,
    page_ptr: PagePtr,
)
    requires
        page_pagetable_wf(pre_pagetable_map, pre_page_array),
        pagetable_perms_wf(post_pagetable_map),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        page_ptr_valid(page_ptr),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
        post_page_array.unchanged_except(
            &pre_page_array,
            page_ptr2page_index(page_ptr),
        ),
        !pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .is_mapped(),
        !post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .is_mapped(),
    ensures
        page_pagetable_wf(post_pagetable_map, post_page_array),
{
    assert(page_pagetable_wf(post_pagetable_map, post_page_array)) by {
        reveal(pagetable_perms_wf);
        reveal(mapped_4k_page_pagetable_wf);
        reveal(mapped_2m_page_pagetable_wf);
        reveal(mapped_1g_page_pagetable_wf);
        assert(page_index2page_ptr(page_ptr2page_index(page_ptr)) == page_ptr) by {
            page_ptr_roundtrip();
        };
        assert forall|page_index: PageIndex, pt_ptr: RwLockPageTableRoot, va: VAddr|
            #![trigger post_page_array.spec_index(page_index).view().view()
                .mappings().contains((pt_ptr, va))]
            page_index_valid(page_index)
            && post_page_array.spec_index(page_index).view().view().state
                == PageState::Mapped4k
            && post_page_array.spec_index(page_index).view().view().mappings()
                .contains((pt_ptr, va))
        implies
            post_pagetable_map.dom().contains(pt_ptr)
            && post_pagetable_map.spec_index(pt_ptr).view().mapping_4k()
                .contains_key(va)
            && post_pagetable_map.spec_index(pt_ptr).view().mapping_4k()
                .spec_index(va).addr == page_index2page_ptr(page_index) by {
            if page_index == page_ptr2page_index(page_ptr) {
            } else if pt_ptr == pagetable_ptr {
            }
        };
        assert forall|pt_ptr: RwLockPageTableRoot, va: VAddr|
            #![trigger post_pagetable_map.spec_index(pt_ptr).view().mapping_4k()
                .contains_key(va)]
            post_pagetable_map.dom().contains(pt_ptr)
            && post_pagetable_map.spec_index(pt_ptr).view().mapping_4k()
                .contains_key(va)
        implies {
            let mapped_page = page_ptr2page_index(
                post_pagetable_map.spec_index(pt_ptr).view().mapping_4k()
                    .spec_index(va).addr,
            );
            &&& post_page_array.spec_index(mapped_page).view().view().state
                == PageState::Mapped4k
            &&& post_page_array.spec_index(mapped_page).view().view().mappings()
                .contains((pt_ptr, va))
        } by {
            let mapped_page = page_ptr2page_index(
                post_pagetable_map.spec_index(pt_ptr).view().mapping_4k()
                    .spec_index(va).addr,
            );
            if pt_ptr == pagetable_ptr {
            }
            if mapped_page == page_ptr2page_index(page_ptr) {
            }
        };
        assert forall|page_index: PageIndex, pt_ptr: RwLockPageTableRoot, va: VAddr|
            #![trigger post_page_array.spec_index(page_index).view().view()
                .mappings().contains((pt_ptr, va))]
            page_index_valid(page_index)
            && post_page_array.spec_index(page_index).view().view().state
                == PageState::Mapped2m
            && post_page_array.spec_index(page_index).view().view().mappings()
                .contains((pt_ptr, va))
        implies
            post_pagetable_map.dom().contains(pt_ptr)
            && post_pagetable_map.spec_index(pt_ptr).view().mapping_2m()
                .contains_key(va)
            && post_pagetable_map.spec_index(pt_ptr).view().mapping_2m()
                .spec_index(va).addr == page_index2page_ptr(page_index) by {
            if page_index == page_ptr2page_index(page_ptr) {
            } else if pt_ptr == pagetable_ptr {
            }
        };
        assert forall|pt_ptr: RwLockPageTableRoot, va: VAddr|
            #![trigger post_pagetable_map.spec_index(pt_ptr).view().mapping_2m()
                .contains_key(va)]
            post_pagetable_map.dom().contains(pt_ptr)
            && post_pagetable_map.spec_index(pt_ptr).view().mapping_2m()
                .contains_key(va)
        implies {
            let mapped_page = page_ptr2page_index(
                post_pagetable_map.spec_index(pt_ptr).view().mapping_2m()
                    .spec_index(va).addr,
            );
            &&& post_page_array.spec_index(mapped_page).view().view().state
                == PageState::Mapped2m
            &&& post_page_array.spec_index(mapped_page).view().view().mappings()
                .contains((pt_ptr, va))
        } by {
            let mapped_page = page_ptr2page_index(
                post_pagetable_map.spec_index(pt_ptr).view().mapping_2m()
                    .spec_index(va).addr,
            );
            if pt_ptr == pagetable_ptr {
            }
            if mapped_page == page_ptr2page_index(page_ptr) {
            }
        };
        assert forall|page_index: PageIndex, pt_ptr: RwLockPageTableRoot, va: VAddr|
            #![trigger post_page_array.spec_index(page_index).view().view()
                .mappings().contains((pt_ptr, va))]
            page_index_valid(page_index)
            && post_page_array.spec_index(page_index).view().view().state
                == PageState::Mapped1g
            && post_page_array.spec_index(page_index).view().view().mappings()
                .contains((pt_ptr, va))
        implies
            post_pagetable_map.dom().contains(pt_ptr)
            && post_pagetable_map.spec_index(pt_ptr).view().mapping_1g()
                .contains_key(va)
            && post_pagetable_map.spec_index(pt_ptr).view().mapping_1g()
                .spec_index(va).addr == page_index2page_ptr(page_index) by {
            if page_index == page_ptr2page_index(page_ptr) {
            } else if pt_ptr == pagetable_ptr {
            }
        };
        assert forall|pt_ptr: RwLockPageTableRoot, va: VAddr|
            #![trigger post_pagetable_map.spec_index(pt_ptr).view().mapping_1g()
                .contains_key(va)]
            post_pagetable_map.dom().contains(pt_ptr)
            && post_pagetable_map.spec_index(pt_ptr).view().mapping_1g()
                .contains_key(va)
        implies {
            let mapped_page = page_ptr2page_index(
                post_pagetable_map.spec_index(pt_ptr).view().mapping_1g()
                    .spec_index(va).addr,
            );
            &&& post_page_array.spec_index(mapped_page).view().view().state
                == PageState::Mapped1g
            &&& post_page_array.spec_index(mapped_page).view().view().mappings()
                .contains((pt_ptr, va))
        } by {
            let mapped_page = page_ptr2page_index(
                post_pagetable_map.spec_index(pt_ptr).view().mapping_1g()
                    .spec_index(va).addr,
            );
            if pt_ptr == pagetable_ptr {
            }
            if mapped_page == page_ptr2page_index(page_ptr) {
            }
        };
    };
}

/// The ownership relation reads only mapped pages and the mapping page table's
/// `proc_ptr`; installing a nonmapped table page changes neither.
pub proof fn container_process_page_pagetable_wf_preserved_for_page_table_page_insert(
    container_map: ContainerLockedMap,
    process_map: ProcessLockedMap,
    pre_pagetable_map: PageTableLockedMap,
    post_pagetable_map: PageTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    pagetable_ptr: RwLockPageTableRoot,
    page_ptr: PagePtr,
)
    requires
        container_process_page_pagetable_wf(
            container_map,
            process_map,
            pre_pagetable_map,
            pre_page_array,
        ),
        page_pagetable_wf(post_pagetable_map, post_page_array),
        process_pagetable_match(process_map, post_pagetable_map),
        container_page_owner_wf(container_map, post_page_array),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        page_ptr_valid(page_ptr),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr
            == pre_pagetable_map.spec_index(pagetable_ptr).view().proc_ptr,
        post_page_array.unchanged_except(
            &pre_page_array,
            page_ptr2page_index(page_ptr),
        ),
        !pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .is_mapped(),
        !post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .is_mapped(),
    ensures
        container_process_page_pagetable_wf(
            container_map,
            process_map,
            post_pagetable_map,
            post_page_array,
        ),
{
    assert(container_process_page_pagetable_wf(
        container_map,
        process_map,
        post_pagetable_map,
        post_page_array,
    )) by {
        reveal(container_process_page_pagetable_wf);
        reveal(mapped_4k_page_pagetable_wf);
        reveal(mapped_2m_page_pagetable_wf);
        reveal(mapped_1g_page_pagetable_wf);
        reveal(process_pagetable_match);
        reveal(container_page_owner_wf);
        assert(page_index2page_ptr(page_ptr2page_index(page_ptr)) == page_ptr) by {
            page_ptr_roundtrip();
        };
        assert forall|page_index: PageIndex, pt_ptr: RwLockPageTableRoot, va: VAddr|
            #![trigger post_page_array.spec_index(page_index).view().view()
                .mappings().contains((pt_ptr, va))]
            page_index_valid(page_index)
            && post_page_array.spec_index(page_index).view().view().is_mapped()
            && post_page_array.spec_index(page_index).view().view().mappings()
                .contains((pt_ptr, va))
        implies {
            ||| process_map.spec_index(
                    post_pagetable_map.spec_index(pt_ptr).view().proc_ptr,
                ).view_rodata().view().owning_container
                == post_page_array.spec_index(page_index).view().view()
                    .owning_container
            ||| container_map.spec_index(
                    post_page_array.spec_index(page_index).view().view()
                        .owning_container,
                ).view().subtree_set.view().contains(
                    process_map.spec_index(
                        post_pagetable_map.spec_index(pt_ptr).view().proc_ptr,
                    ).view_rodata().view().owning_container,
                )
        } by {
            if page_index == page_ptr2page_index(page_ptr) {
            } else if pt_ptr == pagetable_ptr {
            }
        };
    };
}

/// Page-table structure is invisible to the abstract TLB relation.  If all
/// three abstract mapping maps are equal, every cached translation keeps the
/// same backing entry.
pub proof fn tlb_wf_spec_preserved_for_pagetable_mappings_unchanged(
    cpu_tlb: CpuTLB,
    cpu_array: CpuLockedArray,
    pre_pagetable_map: PageTableLockedMap,
    post_pagetable_map: PageTableLockedMap,
    pagetable_ptr: RwLockPageTableRoot,
)
    requires
        tlb_wf_spec(cpu_tlb, pre_pagetable_map, cpu_array),
        pre_pagetable_map.dom().contains(pagetable_ptr),
        post_pagetable_map.unchanged_except(&pre_pagetable_map, pagetable_ptr),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
        post_pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
            == pre_pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
    ensures
        tlb_wf_spec(cpu_tlb, post_pagetable_map, cpu_array),
{
    assert(tlb_wf_spec(cpu_tlb, post_pagetable_map, cpu_array)) by {
        reveal(tlb_wf_spec);
        assert forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger cpu_tlb.spec_index((cpu_id, pcid))]
            cpu_id_valid(cpu_id)
            && pcid_valid(pcid)
            && pcid != KERNEL_DEFAULT_PCID
            && !cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
        implies {
            let dirty_entry = cpu_array.spec_index(cpu_id).view().view()
                .tlb_dirty_bitmap().spec_index(pcid);
            &&& dirty_entry is Some
            &&& post_pagetable_map.dom().contains(
                dirty_entry.unwrap().pagetable_ptr,
            )
            &&& single_cpu_single_pcid_tlb_subset_of_pagetable(
                cpu_tlb.spec_index((cpu_id, pcid)),
                post_pagetable_map.spec_index(
                    dirty_entry.unwrap().pagetable_ptr,
                ).view(),
            )
        } by {
            let dirty_entry = cpu_array.spec_index(cpu_id).view().view()
                .tlb_dirty_bitmap().spec_index(pcid);
            if dirty_entry is Some {
                let dirty_pagetable = dirty_entry.unwrap().pagetable_ptr;
                if dirty_pagetable == pagetable_ptr {
                }
            }
        };
    };
}

/// Retagging one ordinary page as a CPU page-table page cannot affect the
/// disjoint IOMMU-table/page correspondence.
pub proof fn iommu_table_pages_wf_preserved_for_non_iommu_page_change(
    iommu_table_map: IommuTableLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    page_ptr: PagePtr,
)
    requires
        iommu_table_pages_wf(iommu_table_map, pre_page_array),
        page_ptr_valid(page_ptr),
        post_page_array.unchanged_except(
            &pre_page_array,
            page_ptr2page_index(page_ptr),
        ),
        !(pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .state matches PageState::Allocated4k {
                state: Allocated4KPageState::AsIommuTableRoot,
            }),
        !(post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .state matches PageState::Allocated4k {
                state: Allocated4KPageState::AsIommuTableRoot,
            }),
        !(pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .state is IOMMUTable),
        !(post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .state is IOMMUTable),
    ensures
        iommu_table_pages_wf(iommu_table_map, post_page_array),
{
    assert(iommu_table_pages_wf(iommu_table_map, post_page_array)) by {
        reveal(iommu_table_pages_wf);
        assert(page_index2page_ptr(page_ptr2page_index(page_ptr)) == page_ptr) by {
            page_ptr_roundtrip();
        };
    };
}

/// Consume one staged 4K page from exactly one thread.  Quota is deliberately
/// absent: `thread_staged_pages_4k_wf` reads only the cache and `Page::state`;
/// quota conservation is handled by its separate field-framing lemma.
pub proof fn thread_staged_pages_4k_wf_preserved_for_single_consume(
    pre_thread_map: ThreadLockedMap,
    post_thread_map: ThreadLockedMap,
    pre_page_array: PageLockedArray,
    post_page_array: PageLockedArray,
    thread_ptr: RwLockThreadPtr,
    page_ptr: PagePtr,
)
    requires
        thread_staged_pages_4k_wf(pre_thread_map, pre_page_array),
        pre_thread_map.dom().contains(thread_ptr),
        page_ptr_valid(page_ptr),
        post_thread_map.unchanged_except(&pre_thread_map, thread_ptr),
        post_thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
            == pre_thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k
                .view().remove(page_ptr),
        post_page_array.unchanged_except(
            &pre_page_array,
            page_ptr2page_index(page_ptr),
        ),
        pre_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
            == (PageState::Owned4k { thread_ptr }),
        !(post_page_array.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .state is Owned4k),
    ensures
        thread_staged_pages_4k_wf(post_thread_map, post_page_array),
{
    assert(thread_staged_pages_4k_wf(post_thread_map, post_page_array)) by {
        reveal(thread_staged_pages_4k_wf);
        assert(page_index2page_ptr(page_ptr2page_index(page_ptr)) == page_ptr) by {
            page_ptr_roundtrip();
        };
        assert forall|page_index: PageIndex|
            #![trigger post_page_array.spec_index(page_index).view().view().state]
            page_index_wf(page_index)
            && post_page_array.spec_index(page_index).view().view().state is Owned4k
        implies {
            let owner = post_page_array.spec_index(page_index).view().view().state
                ->Owned4k_thread_ptr;
            &&& post_thread_map.dom().contains(owner)
            &&& post_thread_map.spec_index(owner).view().temp_alloc_cache_4k.view()
                .contains(page_index2page_ptr(page_index))
        } by {
            let owner = post_page_array.spec_index(page_index).view().view().state
                ->Owned4k_thread_ptr;
            if page_index == page_ptr2page_index(page_ptr) {
            } else if owner == thread_ptr {
                assert(page_index2page_ptr(page_index) != page_ptr) by {
                    page_index_roundtrip();
                };
            }
        };
        assert forall|owner: RwLockThreadPtr, staged_page: PagePtr|
            #![trigger post_thread_map.spec_index(owner).view()
                .temp_alloc_cache_4k.view().contains(staged_page)]
            post_thread_map.dom().contains(owner)
            && post_thread_map.spec_index(owner).view().temp_alloc_cache_4k.view()
                .contains(staged_page)
        implies
            page_ptr_valid(staged_page)
            && post_page_array.spec_index(page_ptr2page_index(staged_page)).view()
                .view().state == (PageState::Owned4k { thread_ptr: owner }) by {
            if owner == thread_ptr {
            } else if staged_page == page_ptr {
            }
            if page_ptr2page_index(staged_page) == page_ptr2page_index(page_ptr) {
                assert(page_index2page_ptr(page_ptr2page_index(staged_page))
                    == staged_page) by {
                    page_ptr_roundtrip();
                };
            }
        };
    };
}

}
