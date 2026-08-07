use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {

pub proof fn single_tlb_subset_preserved_for_4k_mapping_insert(
    tlb: SingleTLB,
    pre: PageTable<PT_TYPE>,
    post: PageTable<PT_TYPE>,
    va: VAddr,
)
    requires
        single_cpu_single_pcid_tlb_subset_of_pagetable(tlb, pre),
        pre.mapping_4k().dom().contains(va) == false,
        post.mapping_4k().dom().contains(va),
        post.mapping_4k()
            == pre.mapping_4k().insert(va, post.mapping_4k().spec_index(va)),
        post.mapping_2m() == pre.mapping_2m(),
        post.mapping_1g() == pre.mapping_1g(),
    ensures
        single_cpu_single_pcid_tlb_subset_of_pagetable(tlb, post),
{
    assert(single_cpu_single_pcid_tlb_subset_of_pagetable(tlb, post)) by {
        assert forall|mapped_va: VAddr|
            #![trigger post.mapping_4k().dom().contains(mapped_va)]
            #![trigger tlb.tlb_4k().spec_index(mapped_va)]
            tlb.tlb_4k().dom().contains(mapped_va)
            implies
                post.mapping_4k().dom().contains(mapped_va)
                && spec_tlb_entry_equal_to_map_entry(
                    tlb.tlb_4k().spec_index(mapped_va),
                    post.mapping_4k().spec_index(mapped_va),
                ) by {
            if pre.mapping_4k().dom().contains(mapped_va) {
                if mapped_va == va {
                }
            }
        };
        assert forall|mapped_va: VAddr|
            #![trigger post.mapping_2m().dom().contains(mapped_va)]
            #![trigger tlb.tlb_2m().spec_index(mapped_va)]
            tlb.tlb_2m().dom().contains(mapped_va)
            implies
                post.mapping_2m().dom().contains(mapped_va)
                && spec_tlb_entry_equal_to_map_entry(
                    tlb.tlb_2m().spec_index(mapped_va),
                    post.mapping_2m().spec_index(mapped_va),
                ) by {
            if pre.mapping_2m().dom().contains(mapped_va) {
            }
        };
        assert forall|mapped_va: VAddr|
            #![trigger post.mapping_1g().dom().contains(mapped_va)]
            #![trigger tlb.tlb_1g().spec_index(mapped_va)]
            tlb.tlb_1g().dom().contains(mapped_va)
            implies
                post.mapping_1g().dom().contains(mapped_va)
                && spec_tlb_entry_equal_to_map_entry(
                    tlb.tlb_1g().spec_index(mapped_va),
                    post.mapping_1g().spec_index(mapped_va),
                ) by {
            if pre.mapping_1g().dom().contains(mapped_va) {
            }
        };
    };
}

pub proof fn tlb_wf_spec_preserved_for_4k_mapping_insert(
    cpu_tlb: CpuTLB,
    cpu_array: CpuLockedArray,
    pre: PageTableLockedMap,
    post: PageTableLockedMap,
    pagetable_ptr: RwLockPageTableRoot,
    va: VAddr,
)
    requires
        tlb_wf_spec(cpu_tlb, pre, cpu_array),
        pre.dom().contains(pagetable_ptr),
        post.unchanged_except(&pre, pagetable_ptr),
        pre.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va)
            == false,
        post.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va),
        post.spec_index(pagetable_ptr).view().mapping_4k()
            == pre.spec_index(pagetable_ptr).view().mapping_4k().insert(
                va,
                post.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va),
            ),
        post.spec_index(pagetable_ptr).view().mapping_2m()
            == pre.spec_index(pagetable_ptr).view().mapping_2m(),
        post.spec_index(pagetable_ptr).view().mapping_1g()
            == pre.spec_index(pagetable_ptr).view().mapping_1g(),
    ensures
        tlb_wf_spec(cpu_tlb, post, cpu_array),
{
    reveal(tlb_wf_spec);
    assert forall|cpu_id: CpuId, pcid: Pcid|
        #![trigger cpu_tlb.spec_index((cpu_id, pcid))]
        cpu_id_valid(cpu_id)
        && pcid_valid(pcid)
        && pcid != KERNEL_DEFAULT_PCID
        && cpu_tlb.spec_index((cpu_id, pcid)).is_empty() == false
        implies single_cpu_single_pcid_tlb_subset_of_pagetable(
            cpu_tlb.spec_index((cpu_id, pcid)),
            post.spec_index(
                cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap()
                    .spec_index(pcid).unwrap().pagetable_ptr,
            ).view(),
        ) by {
        let dirty_entry = cpu_array.spec_index(cpu_id).view().view()
            .tlb_dirty_bitmap().spec_index(pcid);
        if dirty_entry is Some {
            let dirty_pagetable = dirty_entry.unwrap().pagetable_ptr;
            if dirty_pagetable == pagetable_ptr {
                assert(single_cpu_single_pcid_tlb_subset_of_pagetable(
                    cpu_tlb.spec_index((cpu_id, pcid)),
                    post.spec_index(dirty_pagetable).view(),
                )) by { single_tlb_subset_preserved_for_4k_mapping_insert(cpu_tlb.spec_index((cpu_id, pcid)), pre.spec_index(dirty_pagetable).view(), post.spec_index(dirty_pagetable).view(), va); };
            }
        }
    };
}

}
