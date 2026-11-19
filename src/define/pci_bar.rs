use vstd::prelude::*;
use crate::*;

verus! {
/// A PCI BAR slot: the function's bus/device/function and the BAR index (0 to 5).
pub type BarKey = (PciBdf, usize);

/// The exact byte range of one BAR.
pub ghost struct BarRegion {
    pub start: PAddr,
    pub len: usize,
}

impl BarRegion {
    pub open spec fn wf(&self) -> bool {
        &&& self.len > 0
        &&& self.start as int + self.len as int <= MEM_4K_MASK as int + PAGE_SZ_4K as int
    }

    /// The first 4K page base of the region's outward-rounded page envelope.
    pub open spec fn first_page(&self) -> int { self.start as int / PAGE_SZ_4K as int * PAGE_SZ_4K as int }

    /// The 4K page base `p` lies in the region's outward-rounded page envelope.
    pub open spec fn envelope_contains(&self, p: PAddr) -> bool {
        &&& p % PAGE_SZ_4K == 0
        &&& self.first_page() <= p as int
        &&& (p as int) < self.start as int + self.len as int
    }
}

/// The BAR slots of every PCI function, filled once at boot. Sealed: verified code reads them through `view` and can
/// neither build nor change one.
pub struct PciBarSlots {
    bars: Ghost<Map<BarKey, BarRegion>>,
}

impl PciBarSlots {
    /// Present slots; an absent key is an empty slot.
    pub closed spec fn view(&self) -> Map<BarKey, BarRegion> { self.bars.view() }

    /// Callable only from the unverified boot glue; `requires false` keeps verified code out.
    pub fn new(Ghost(bars): Ghost<Map<BarKey, BarRegion>>) -> (ret: Self)
        requires false,
        ensures ret.view() == bars,
    {
        Self { bars: Ghost(bars) }
    }
}
}
