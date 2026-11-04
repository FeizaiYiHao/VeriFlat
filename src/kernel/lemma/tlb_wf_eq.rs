use vstd::prelude::*;
use crate::*;
use crate::kernel::*;

verus! {
/// The CPU TLB invariant carries over the install of the 4K leaf `va` into page table `pagetable_ptr`: no leaf was held at
/// `va` before, every other held leaf, the big-lock payload and the stale-CPU records are unchanged, and the user mappings
/// change only at `va`.
pub proof fn tlb_wf_spec_preserved_for_4k_mapping_insert(cpu_tlb: CpuTLB, cpu_array: CpuLockedArray, pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap,
    post_pt: PageTableLockedMap, post_lower: PageTableLowerMap, pagetable_ptr: RwLockPageTableRoot, va: VAddr, needflush: PcidNeedFlushArray)
    requires
        tlb_wf_spec(cpu_tlb, pre_pt, pre_lower, cpu_array, needflush),
        pre_pt.dom().contains(pagetable_ptr),
        post_pt.unchanged_except(&pre_pt, pagetable_ptr),
        post_lower == pre_lower.insert(pagetable_ptr, post_lower.spec_index(pagetable_ptr)),
        post_pt.spec_index(pagetable_ptr).view() == pre_pt.spec_index(pagetable_ptr).view(),
        whole_pagetable(pre_pt, pre_lower, pagetable_ptr).wf(),
        whole_pagetable(post_pt, post_lower, pagetable_ptr).wf(),
        whole_pagetable(post_pt, post_lower, pagetable_ptr).lower.window_stale_cpus == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).lower.window_stale_cpus,
        va_4k_valid(va),
        whole_pagetable(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre_pt, pre_lower, pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
        whole_pagetable(pre_pt, pre_lower, pagetable_ptr).mapping_4k().dom().contains(va) == false,
        whole_pagetable(post_pt, post_lower, pagetable_ptr).mapping_4k() == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).mapping_4k().insert(va, whole_pagetable(post_pt, post_lower, pagetable_ptr).mapping_4k().spec_index(va)),
        whole_pagetable(post_pt, post_lower, pagetable_ptr).mapping_2m() == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).mapping_2m(),
        whole_pagetable(post_pt, post_lower, pagetable_ptr).mapping_1g() == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).mapping_1g(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(post_pt, post_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
            && (l4i, l3i, l2i, l1i) != spec_va2index(va) ==> whole_pagetable(post_pt, post_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i) == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(post_pt, post_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(pre_pt, pre_lower, pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(post_pt, post_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i) == whole_pagetable(pre_pt, pre_lower, pagetable_ptr).spec_held_2m_l2(l4i, l3i, l2i),
    ensures
        tlb_wf_spec(cpu_tlb, post_pt, post_lower, cpu_array, needflush),
{
    let old_pt = whole_pagetable(pre_pt, pre_lower, pagetable_ptr);
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
    assert(old_pt.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None) by {
        old_pt.wf_mapping_4k_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
        old_pt.spec_resolve_mapping_l2_some_implies_spec_held_l2_eq(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
        old_pt.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(spec_v2l4index(va), spec_v2l3index(va));
    };
    reveal(tlb_wf_spec); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m);
}
}
