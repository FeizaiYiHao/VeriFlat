use vstd::prelude::*;

verus! {
use crate::*;

pub open spec fn spec_l2_index_path_le(lhs: (L2Index, L1Index), rhs: (L2Index, L1Index)) -> bool { lhs.0 < rhs.0 || (lhs.0 == rhs.0 && lhs.1 <= rhs.1) }

pub open spec fn spec_l3_index_path_le(lhs: (L3Index, L2Index, L1Index), rhs: (L3Index, L2Index, L1Index)) -> bool {
    lhs.0 < rhs.0 || (lhs.0 == rhs.0 && spec_l2_index_path_le((lhs.1, lhs.2), (rhs.1, rhs.2)))
}

pub open spec fn spec_l4_index_path_le(lhs: (L4Index, L3Index, L2Index, L1Index), rhs: (L4Index, L3Index, L2Index, L1Index)) -> bool {
    lhs.0 < rhs.0 || (lhs.0 == rhs.0 && spec_l3_index_path_le((lhs.1, lhs.2, lhs.3), (rhs.1, rhs.2, rhs.3)))
}

/// An index path strictly below the L1 successor `succ` of `n` is `n` itself or strictly below `n`.
pub proof fn index_path_successor_implies_path_le_drops_only_predecessor(n: (L4Index, L3Index, L2Index, L1Index), succ: (L4Index, L3Index, L2Index, L1Index))
    requires
        n.3 < 512,
        succ == (n.0, n.1, n.2, (n.3 + 1) as usize),
    ensures
        forall|idx: (L4Index, L3Index, L2Index, L1Index)| #![trigger spec_l4_index_path_le(succ, idx)] !spec_l4_index_path_le(succ, idx) ==> idx == n || !spec_l4_index_path_le(n, idx),
{
}
} // verus!
