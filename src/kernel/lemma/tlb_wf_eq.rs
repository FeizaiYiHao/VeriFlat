use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {
pub proof fn tlb_wf_spec_preserved_for_4k_mapping_insert(cpu_tlb: CpuTLB, cpu_array: CpuLockedArray, pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap,
    post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr, needflush: PcidNeedFlushArray)
    requires
        tlb_wf_spec(cpu_tlb, pre_pt, pre_lower, cpu_array, needflush),
        pre_pt.dom().contains(pagetable_ptr),
        post_pt.unchanged_except(&pre_pt, pagetable_ptr),
        post_lower == pre_lower.insert(pagetable_ptr, post_lower.spec_index(pagetable_ptr)),
        post_pt.spec_index(pagetable_ptr).view() == pre_pt.spec_index(pagetable_ptr).view(),
        pagetable_c(post_pt, post_lower, pagetable_ptr).lower.window_stale_cpus == pagetable_c(pre_pt, pre_lower, pagetable_ptr).lower.window_stale_cpus,
        pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_4k().dom().contains(va) == false,
        pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_4k().dom().contains(va),
        pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_4k() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_4k().insert(va, pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_4k().spec_index(va)),
        pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_2m() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_2m(),
        pagetable_c(post_pt, post_lower, pagetable_ptr).mapping_1g() == pagetable_c(pre_pt, pre_lower, pagetable_ptr).mapping_1g(),
    ensures
        tlb_wf_spec(cpu_tlb, post_pt, post_lower, cpu_array, needflush),
{ reveal(tlb_wf_spec); }
}
