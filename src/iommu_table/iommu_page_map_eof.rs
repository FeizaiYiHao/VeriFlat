use vstd::prelude::*;
verus! {
use crate::*;

pub(super) open spec fn iommu_page_map_set_eof_transition_framing(pre: IommuPageMap, post: IommuPageMap, index: usize, value: PageEntry, raw: usize) -> bool {
    &&& post.ar.view() =~= pre.ar.view().update(index as int, raw)
    &&& post.spec_seq.view() =~= pre.spec_seq.view().update(index as int, value)
}

pub(super) proof fn iommu_page_map_set_eof_implies_wf(pre: IommuPageMap, post: IommuPageMap, index: usize, value: PageEntry, raw: usize)
    requires
        pre.iommu_wf(),
        pei_valid(index),
        mem_valid(value.addr),
        !value.perm.ps,
        !value.perm.user,
        value.perm.write ==> value.perm.present,
        iommu_word_valid(raw),
        spec_usize2page_entry(raw) =~= value,
        post.ar.wf(),
        iommu_page_map_set_eof_transition_framing(pre, post, index, value, raw),
    ensures post.iommu_wf(),
{
}
} // verus!
