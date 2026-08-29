use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {
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
}

}
