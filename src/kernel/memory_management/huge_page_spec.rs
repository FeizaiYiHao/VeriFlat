use vstd::prelude::*;
use crate::*;

verus! {
/// The 2M head states (Free2m, Owned2m, Allocated2m, Mapped2m) and the 2M tail state Merged2m.
pub open spec fn page_state_2m_related(s: PageState) -> bool {
    ||| s is Free2m
    ||| s is Owned2m
    ||| s is Allocated2m
    ||| s is Mapped2m
    ||| s is Merged2m
}

/// The 1G head states (Free1g, Mapped1g) and the 1G tail state Merged1g.
pub open spec fn page_state_1g_related(s: PageState) -> bool {
    ||| s is Free1g
    ||| s is Mapped1g
    ||| s is Merged1g
}

/// A 2M head page is 2M-aligned.
pub open spec fn hugepage_2m_head_aligned_wf(pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state is Free2m]
        #![trigger pg_arr.spec_index(p_i).view().view().state is Owned2m]
        #![trigger pg_arr.spec_index(p_i).view().view().state is Allocated2m]
        #![trigger pg_arr.spec_index(p_i).view().view().state is Mapped2m]
        #![trigger page_index_2m_valid(p_i)]
        index_valid(NUM_PAGES, p_i)
            && {
                ||| pg_arr.spec_index(p_i).view().view().state is Free2m
                ||| pg_arr.spec_index(p_i).view().view().state is Owned2m
                ||| pg_arr.spec_index(p_i).view().view().state is Allocated2m
                ||| pg_arr.spec_index(p_i).view().view().state is Mapped2m
            }
            ==>
            page_index_2m_valid(p_i)
}

/// Each page in a 2M head's region is a Merged2m tail.
// Proof dependencies (confirmed): hugepage_2m_head_aligned_wf.
pub open spec fn hugepage_2m_tail_forward_wf(pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex, p_j: PageIndex|
        #![trigger spec_page_index_merge_2m_valid(p_i, p_j)]
        #![trigger pg_arr.spec_index(p_i).view().view().state is Free2m, pg_arr.spec_index(p_j).view().view().state is Merged2m]
        #![trigger pg_arr.spec_index(p_i).view().view().state is Owned2m, pg_arr.spec_index(p_j).view().view().state is Merged2m]
        #![trigger pg_arr.spec_index(p_i).view().view().state is Allocated2m, pg_arr.spec_index(p_j).view().view().state is Merged2m]
        #![trigger pg_arr.spec_index(p_i).view().view().state is Mapped2m, pg_arr.spec_index(p_j).view().view().state is Merged2m]
        index_valid(NUM_PAGES, p_i)
            && index_valid(NUM_PAGES, p_j)
            && {
                ||| pg_arr.spec_index(p_i).view().view().state is Free2m
                ||| pg_arr.spec_index(p_i).view().view().state is Owned2m
                ||| pg_arr.spec_index(p_i).view().view().state is Allocated2m
                ||| pg_arr.spec_index(p_i).view().view().state is Mapped2m
            }
            && spec_page_index_merge_2m_valid(p_i, p_j)
            ==> pg_arr.spec_index(p_j).view().view().state is Merged2m
}

/// A Merged2m tail's region head is in a 2M head state.
pub open spec fn hugepage_2m_tail_backward_wf(pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state is Merged2m]
        #![trigger spec_page_index_truncate_2m(p_i)]
        index_valid(NUM_PAGES, p_i) && (pg_arr.spec_index(p_i).view().view().state is Merged2m) ==> {
            ||| pg_arr.spec_index(spec_page_index_truncate_2m(p_i)).view().view().state is Free2m
            ||| pg_arr.spec_index(spec_page_index_truncate_2m(p_i)).view().view().state is Owned2m
            ||| pg_arr.spec_index(spec_page_index_truncate_2m(p_i)).view().view().state is Allocated2m
            ||| pg_arr.spec_index(spec_page_index_truncate_2m(p_i)).view().view().state is Mapped2m
        }
}

/// 2M head pages are 2M-aligned, and 2M regions and their Merged2m tails agree in both directions.
#[verifier::opaque]
pub open spec fn hugepage_2m_wf(pg_arr: PageLockedArray) -> bool {
    &&& hugepage_2m_head_aligned_wf(pg_arr)
    &&& hugepage_2m_tail_forward_wf(pg_arr)
    &&& hugepage_2m_tail_backward_wf(pg_arr)
}

/// Page `tail_idx` inside the 2M region headed by the 2M head page `head_idx` is merged into it.
pub proof fn hugepage_2m_wf_tail_forward_at(pg_arr: PageLockedArray, head_idx: PageIndex, tail_idx: PageIndex)
    requires
        hugepage_2m_wf(pg_arr),
    ensures
        index_valid(NUM_PAGES, head_idx)
            && index_valid(NUM_PAGES, tail_idx)
            && {
                ||| pg_arr.spec_index(head_idx).view().view().state is Free2m
                ||| pg_arr.spec_index(head_idx).view().view().state is Owned2m
                ||| pg_arr.spec_index(head_idx).view().view().state is Allocated2m
                ||| pg_arr.spec_index(head_idx).view().view().state is Mapped2m
            }
            && spec_page_index_merge_2m_valid(head_idx, tail_idx)
            ==> pg_arr.spec_index(tail_idx).view().view().state is Merged2m,
{ reveal(hugepage_2m_wf); }

/// A 2M head page `pg_idx` starts a 2M-aligned region.
pub proof fn hugepage_2m_wf_head_at(pg_arr: PageLockedArray, pg_idx: PageIndex)
    requires
        hugepage_2m_wf(pg_arr),
    ensures
        index_valid(NUM_PAGES, pg_idx)
            && {
                ||| pg_arr.spec_index(pg_idx).view().view().state is Free2m
                ||| pg_arr.spec_index(pg_idx).view().view().state is Owned2m
                ||| pg_arr.spec_index(pg_idx).view().view().state is Allocated2m
                ||| pg_arr.spec_index(pg_idx).view().view().state is Mapped2m
            }
            ==> page_index_2m_valid(pg_idx),
{ reveal(hugepage_2m_wf); }

/// A 1G head page is 1G-aligned.
pub open spec fn hugepage_1g_head_aligned_wf(pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state is Free1g]
        #![trigger pg_arr.spec_index(p_i).view().view().state is Mapped1g]
        #![trigger page_index_1g_valid(p_i)]
        index_valid(NUM_PAGES, p_i)
            && {
                ||| pg_arr.spec_index(p_i).view().view().state is Free1g
                ||| pg_arr.spec_index(p_i).view().view().state is Mapped1g
            }
            ==>
            page_index_1g_valid(p_i)
}

/// Each page in a 1G head's region is a Merged1g tail.
pub open spec fn hugepage_1g_tail_forward_wf(pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex, p_j: PageIndex|
        #![trigger spec_page_index_merge_1g_valid(p_i, p_j)]
        #![trigger pg_arr.spec_index(p_i).view().view().state is Free1g, pg_arr.spec_index(p_j).view().view().state is Merged1g]
        #![trigger pg_arr.spec_index(p_i).view().view().state is Mapped1g, pg_arr.spec_index(p_j).view().view().state is Merged1g]
        index_valid(NUM_PAGES, p_i)
            && index_valid(NUM_PAGES, p_j)
            && {
                ||| pg_arr.spec_index(p_i).view().view().state is Free1g
                ||| pg_arr.spec_index(p_i).view().view().state is Mapped1g
            }
            && spec_page_index_merge_1g_valid(p_i, p_j)
            ==> pg_arr.spec_index(p_j).view().view().state is Merged1g
}

/// A Merged1g tail's region head is in a 1G head state.
pub open spec fn hugepage_1g_tail_backward_wf(pg_arr: PageLockedArray) -> bool {
    forall|p_i: PageIndex|
        #![trigger pg_arr.spec_index(p_i).view().view().state is Merged1g]
        #![trigger spec_page_index_truncate_1g(p_i)]
        index_valid(NUM_PAGES, p_i) && (pg_arr.spec_index(p_i).view().view().state is Merged1g) ==> {
            ||| pg_arr.spec_index(spec_page_index_truncate_1g(p_i)).view().view().state is Free1g
            ||| pg_arr.spec_index(spec_page_index_truncate_1g(p_i)).view().view().state is Mapped1g
        }
}

/// 1G head pages are 1G-aligned, and 1G regions and their Merged1g tails agree in both directions.
#[verifier::opaque]
pub open spec fn hugepage_1g_wf(pg_arr: PageLockedArray) -> bool {
    &&& hugepage_1g_head_aligned_wf(pg_arr)
    &&& hugepage_1g_tail_forward_wf(pg_arr)
    &&& hugepage_1g_tail_backward_wf(pg_arr)
}

/// A free or mapped 1G head page `pg_idx` starts a 1G-aligned region.
pub proof fn hugepage_1g_wf_head_at(pg_arr: PageLockedArray, pg_idx: PageIndex)
    requires
        hugepage_1g_wf(pg_arr),
    ensures
        index_valid(NUM_PAGES, pg_idx)
            && {
                ||| pg_arr.spec_index(pg_idx).view().view().state is Free1g
                ||| pg_arr.spec_index(pg_idx).view().view().state is Mapped1g
            }
            ==> page_index_1g_valid(pg_idx),
{ reveal(hugepage_1g_wf); }

/// Page `tail_idx` inside the 1G region headed by the free or mapped page `head_idx` is merged into it.
pub proof fn hugepage_1g_wf_tail_forward_at(pg_arr: PageLockedArray, head_idx: PageIndex, tail_idx: PageIndex)
    requires
        hugepage_1g_wf(pg_arr),
    ensures
        index_valid(NUM_PAGES, head_idx)
            && index_valid(NUM_PAGES, tail_idx)
            && {
                ||| pg_arr.spec_index(head_idx).view().view().state is Free1g
                ||| pg_arr.spec_index(head_idx).view().view().state is Mapped1g
            }
            && spec_page_index_merge_1g_valid(head_idx, tail_idx)
            ==> pg_arr.spec_index(tail_idx).view().view().state is Merged1g,
{ reveal(hugepage_1g_wf); }
}
