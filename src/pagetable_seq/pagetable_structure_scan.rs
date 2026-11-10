use vstd::prelude::*;

verus! {
use crate::*;

/// A table page that a page table can unlink bottom-up, or why it has none.
#[derive(Clone, Copy)]
pub enum StructureScan {
    /// The L1 table `l1_p`, linked from entry `l2i` of the L2 table `l2_p` at `(l4i, l3i)`, records no 4K leaf.
    L1 { l4i: L4Index, l3i: L3Index, l2i: L2Index, l2_p: PageMapPtr, l1_p: PageMapPtr },
    /// The L2 table `l2_p`, linked from entry `l3i` of the L3 table `l3_p` at `l4i`, links nothing.
    L2 { l4i: L4Index, l3i: L3Index, l3_p: PageMapPtr, l2_p: PageMapPtr },
    /// The L3 table `l3_p`, linked from the user L4 entry `l4i`, links nothing.
    L3 { l4i: L4Index, l3_p: PageMapPtr },
    /// No user L4 entry is present, so the root is the only table page.
    Empty,
    /// A leaf is recorded, so no table page can be unlinked.
    Blocked,
}

impl StructureScan {
    /// The table page the scan names, if any.
    pub open spec fn spec_table_page(&self) -> Option<PageMapPtr> {
        match *self {
            StructureScan::L1 { l1_p, .. } => Some(l1_p),
            StructureScan::L2 { l2_p, .. } => Some(l2_p),
            StructureScan::L3 { l3_p, .. } => Some(l3_p),
            _ => None,
        }
    }

    /// The table page the scan names, if any.
    #[verifier::when_used_as_spec(spec_table_page)]
    pub fn table_page(&self) -> (ret: Option<PageMapPtr>)
        ensures ret == self.spec_table_page(),
    {
        match self {
            StructureScan::L1 { l1_p, .. } => Some(*l1_p),
            StructureScan::L2 { l2_p, .. } => Some(*l2_p),
            StructureScan::L3 { l3_p, .. } => Some(*l3_p),
            _ => None,
        }
    }
}
} // verus!
