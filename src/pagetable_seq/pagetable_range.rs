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

/// An index path at or below another in `spec_l4_index_path_le` order names a 4K virtual address at or below the other's.
pub broadcast proof fn spec_l4_index_path_le_implies_spec_index2va_le(lhs: (L4Index, L3Index, L2Index, L1Index), rhs: (L4Index, L3Index, L2Index, L1Index))
    requires
        pei_valid(lhs.0), pei_valid(lhs.1), pei_valid(lhs.2), pei_valid(lhs.3),
        pei_valid(rhs.0), pei_valid(rhs.1), pei_valid(rhs.2), pei_valid(rhs.3),
        #[trigger] spec_l4_index_path_le(lhs, rhs),
    ensures spec_index2va(lhs) <= spec_index2va(rhs),
{ if spec_index2va(rhs) < spec_index2va(lhs) { spec_index2va_le_implies_4k_indices_lex_le(rhs, lhs); } }

/// The position of an index path in the order of `spec_l4_index_path_le`, counting the L1 index up to 512 inclusive:
/// 134,479,872 = 512 * 512 * 513 and 262,656 = 512 * 513.
pub open spec fn spec_l4_index_path_rank(c: (L4Index, L3Index, L2Index, L1Index)) -> nat { c.0 as nat * 134_479_872 + c.1 as nat * 262_656 + c.2 as nat * 513 + c.3 as nat }

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
