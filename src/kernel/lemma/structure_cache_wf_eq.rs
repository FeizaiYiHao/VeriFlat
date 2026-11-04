use vstd::prelude::*;
use crate::*;

verus! {
/// The paging-structure invariant carries over an operation that keeps the paging-structure caches, every CPU's dirty
/// records and current PCID, the flush marks, and in every page table the big-lock payload, the L2 entries, the held L2
/// entries of user paths, and the window stale-CPU records.
pub proof fn structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre: KernelK, post: KernelK)
    requires
        structure_cache_wf_spec(pre.cpu_tlb, pre.pt_mp, pre.pt_lower.view(), pre.cpu_arr, pre.pcid_needflush),
        post.cpu_tlb.structure_caches.view() == pre.cpu_tlb.structure_caches.view(),
        forall|c: CpuId| #![trigger post.cpu_arr.spec_index(c)] index_valid(NUM_CPUS, c)
            ==> post.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap() == pre.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap()
            && post.cpu_arr.spec_index(c).view().view().view().current_pcid == pre.cpu_arr.spec_index(c).view().view().view().current_pcid,
        forall|c: CpuId, p: Pcid| #![trigger post.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p)
            ==> post.pcid_needflush.spec_index(c, p).view().needflush == pre.pcid_needflush.spec_index(c, p).view().needflush,
        forall|t: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), t)] pre.pt_mp.dom().contains(t) ==> {
            let before = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), t);
            let after = whole_pagetable(post.pt_mp, post.pt_lower.view(), t);
            &&& post.pt_mp.dom().contains(t)
            &&& after.higher == before.higher
            &&& after.lower.window_stale_cpus == before.lower.window_stale_cpus
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger after.lower.l2_entry(p, i)] after.lower.l2_entry(p, i) == before.lower.l2_entry(p, i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger after.spec_held_l2(l4i, l3i, l2i)]
                before.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> after.spec_held_l2(l4i, l3i, l2i) == before.spec_held_l2(l4i, l3i, l2i)
        },
    ensures structure_cache_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{ reveal(structure_cache_wf_spec); }
}
