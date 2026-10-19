use vstd::prelude::*;
use crate::*;

verus! {
    // A page slot participates in the 2m hugepage invariant iff its state is one
    // of the 2m variants (the leaf 2m states or a 2m merge tail). Used to scope
    // the `hugepage_2m_wf` framing lemma to exactly the slots that invariant reads.
    pub open spec fn page_state_2m_related(s: PageState) -> bool {
        ||| s is Free2m
        ||| s is Owned2m
        ||| s is Allocated2m
        ||| s is Mapped2m
        ||| s is Merged2m
    }

    // 1g twin of `page_state_2m_related`.
    pub open spec fn page_state_1g_related(s: PageState) -> bool {
        ||| s is Free1g
        ||| s is Mapped1g
        ||| s is Merged1g
    }

    pub open spec fn hugepage_2m_head_valid_wf(page_array: PageLockedArray) -> bool {
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state is Free2m]
            #![trigger page_array.spec_index(p_i).view().view().state is Owned2m]
            #![trigger page_array.spec_index(p_i).view().view().state is Allocated2m]
            #![trigger page_array.spec_index(p_i).view().view().state is Mapped2m]
            #![trigger page_index_2m_valid(p_i)]
            index_valid(NUM_PAGES, p_i) && {
                ||| page_array.spec_index(p_i).view().view().state is Free2m
                ||| page_array.spec_index(p_i).view().view().state is Owned2m
                ||| page_array.spec_index(p_i).view().view().state is Allocated2m
                ||| page_array.spec_index(p_i).view().view().state is Mapped2m
            } ==> page_index_2m_valid(p_i)
    }

    // Proof dependencies (confirmed): hugepage_2m_head_valid_wf.
    pub open spec fn hugepage_2m_tail_forward_wf(page_array: PageLockedArray) -> bool {
        forall|p_i:PageIndex, p_j:PageIndex|
            #![trigger spec_page_index_merge_2m_valid(p_i, p_j)]
            #![trigger page_array.spec_index(p_i).view().view().state is Free2m, page_array.spec_index(p_j).view().view().state is Merged2m]
            #![trigger page_array.spec_index(p_i).view().view().state is Owned2m, page_array.spec_index(p_j).view().view().state is Merged2m]
            #![trigger page_array.spec_index(p_i).view().view().state is Allocated2m, page_array.spec_index(p_j).view().view().state is Merged2m]
            #![trigger page_array.spec_index(p_i).view().view().state is Mapped2m, page_array.spec_index(p_j).view().view().state is Merged2m]
            index_valid(NUM_PAGES, p_i) && index_valid(NUM_PAGES, p_j) && {
                ||| page_array.spec_index(p_i).view().view().state is Free2m
                ||| page_array.spec_index(p_i).view().view().state is Owned2m
                ||| page_array.spec_index(p_i).view().view().state is Allocated2m
                ||| page_array.spec_index(p_i).view().view().state is Mapped2m
            } && spec_page_index_merge_2m_valid(p_i, p_j) ==> {
                &&& page_array.spec_index(p_j).view().view().state is Merged2m
                &&& page_array.spec_index(p_j).view().view().owning_container == page_array.spec_index(p_i).view().view().owning_container
            }
    }

    pub open spec fn hugepage_2m_tail_backward_wf(page_array: PageLockedArray) -> bool {
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state is Merged2m]
            #![trigger spec_page_index_truncate_2m(p_i)]
            index_valid(NUM_PAGES, p_i) && (page_array.spec_index(p_i).view().view().state is Merged2m) ==> {
                ||| page_array.spec_index(spec_page_index_truncate_2m(p_i)).view().view().state is Free2m
                ||| page_array.spec_index(spec_page_index_truncate_2m(p_i)).view().view().state is Owned2m
                ||| page_array.spec_index(spec_page_index_truncate_2m(p_i)).view().view().state is Allocated2m
                ||| page_array.spec_index(spec_page_index_truncate_2m(p_i)).view().view().state is Mapped2m
            }
    }

    #[verifier::opaque]
    pub open spec fn hugepage_2m_wf(page_array: PageLockedArray) -> bool {
        &&& hugepage_2m_head_valid_wf(page_array)
        &&& hugepage_2m_tail_forward_wf(page_array)
        &&& hugepage_2m_tail_backward_wf(page_array)
    }

    pub proof fn hugepage_2m_wf_tail_at(page_array: PageLockedArray, p_i: PageIndex, p_j: PageIndex)
        requires
            hugepage_2m_wf(page_array),
        ensures
            index_valid(NUM_PAGES, p_i) && index_valid(NUM_PAGES, p_j) && {
                ||| page_array.spec_index(p_i).view().view().state is Free2m
                ||| page_array.spec_index(p_i).view().view().state is Owned2m
                ||| page_array.spec_index(p_i).view().view().state is Allocated2m
                ||| page_array.spec_index(p_i).view().view().state is Mapped2m
            } && spec_page_index_merge_2m_valid(p_i, p_j) ==> {
                &&& page_array.spec_index(p_j).view().view().state is Merged2m
                &&& page_array.spec_index(p_j).view().view().owning_container == page_array.spec_index(p_i).view().view().owning_container
            },
    { reveal(hugepage_2m_wf); }

    /// A 2m head page `p_i` starts a 2m-aligned region.
    pub proof fn hugepage_2m_wf_head_at(page_array: PageLockedArray, p_i: PageIndex)
        requires
            hugepage_2m_wf(page_array),
        ensures
            index_valid(NUM_PAGES, p_i) && {
                ||| page_array.spec_index(p_i).view().view().state is Free2m
                ||| page_array.spec_index(p_i).view().view().state is Owned2m
                ||| page_array.spec_index(p_i).view().view().state is Allocated2m
                ||| page_array.spec_index(p_i).view().view().state is Mapped2m
            } ==> page_index_2m_valid(p_i),
    { reveal(hugepage_2m_wf); }

    pub open spec fn hugepage_1g_head_valid_wf(page_array: PageLockedArray) -> bool {
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state is Free1g]
            #![trigger page_array.spec_index(p_i).view().view().state is Mapped1g]
            #![trigger page_index_1g_valid(p_i)]
            index_valid(NUM_PAGES, p_i) && { page_array.spec_index(p_i).view().view().state is Free1g || page_array.spec_index(p_i).view().view().state is Mapped1g } ==> page_index_1g_valid(p_i)
    }

    pub open spec fn hugepage_1g_tail_forward_wf(page_array: PageLockedArray) -> bool {
        forall|p_i:PageIndex, p_j:PageIndex|
            #![trigger spec_page_index_merge_1g_valid(p_i, p_j)]
            #![trigger page_array.spec_index(p_i).view().view().state is Free1g, page_array.spec_index(p_j).view().view().state is Merged1g]
            #![trigger page_array.spec_index(p_i).view().view().state is Mapped1g, page_array.spec_index(p_j).view().view().state is Merged1g]
            index_valid(NUM_PAGES, p_i) && index_valid(NUM_PAGES, p_j) && {
                ||| page_array.spec_index(p_i).view().view().state is Free1g
                ||| page_array.spec_index(p_i).view().view().state is Mapped1g
            } && spec_page_index_merge_1g_valid(p_i, p_j) ==> {
                &&& page_array.spec_index(p_j).view().view().state is Merged1g
                &&& page_array.spec_index(p_j).view().view().owning_container == page_array.spec_index(p_i).view().view().owning_container
            }
    }

    pub open spec fn hugepage_1g_tail_backward_wf(page_array: PageLockedArray) -> bool {
        forall|p_i:PageIndex|
            #![trigger page_array.spec_index(p_i).view().view().state is Merged1g]
            #![trigger spec_page_index_truncate_1g(p_i)]
            index_valid(NUM_PAGES, p_i) && (page_array.spec_index(p_i).view().view().state is Merged1g) ==> {
                ||| page_array.spec_index(spec_page_index_truncate_1g(p_i)).view().view().state is Free1g
                ||| page_array.spec_index(spec_page_index_truncate_1g(p_i)).view().view().state is Mapped1g
            }
    }

    #[verifier::opaque]
    pub open spec fn hugepage_1g_wf(page_array: PageLockedArray) -> bool {
        &&& hugepage_1g_head_valid_wf(page_array)
        &&& hugepage_1g_tail_forward_wf(page_array)
        &&& hugepage_1g_tail_backward_wf(page_array)
    }

    /// A free or mapped 1G head page `p_i` starts a 1G-aligned region.
    pub proof fn hugepage_1g_wf_head_at(page_array: PageLockedArray, p_i: PageIndex)
        requires
            hugepage_1g_wf(page_array),
        ensures
            index_valid(NUM_PAGES, p_i) && (page_array.spec_index(p_i).view().view().state is Free1g || page_array.spec_index(p_i).view().view().state is Mapped1g) ==> page_index_1g_valid(p_i),
    { reveal(hugepage_1g_wf); }

    /// Page `p_j` inside the 1G region headed by the free or mapped page `p_i` is merged into it.
    pub proof fn hugepage_1g_wf_tail_forward_at(page_array: PageLockedArray, p_i: PageIndex, p_j: PageIndex)
        requires
            hugepage_1g_wf(page_array),
        ensures
            index_valid(NUM_PAGES, p_i) && index_valid(NUM_PAGES, p_j) && (page_array.spec_index(p_i).view().view().state is Free1g || page_array.spec_index(p_i).view().view().state is Mapped1g)
                && spec_page_index_merge_1g_valid(p_i, p_j) ==> page_array.spec_index(p_j).view().view().state is Merged1g,
    { reveal(hugepage_1g_wf); }
}
