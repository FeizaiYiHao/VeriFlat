use vstd::prelude::*;
use crate::*;

verus! {
/// One memory BAR of one PCI function: the function's bus/device/function, the BAR index (0 to 5; a 64-bit BAR is keyed
/// by its low register), and the BAR's exact byte range `[base, base + size)`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct PciBarEntry {
    pub bdf: PciBdf,
    pub bar: usize,
    pub base: PAddr,
    pub size: usize,
}

impl PciBarEntry {
    /// A valid PCI function, a BAR index below 6, and a nonempty byte range ending at or below `MEM_4K_MASK + 4K`.
    pub open spec fn wf(&self) -> bool {
        &&& pci_bdf_valid(self.bdf.0, self.bdf.1, self.bdf.2)
        &&& self.bar < 6
        &&& self.size > 0
        &&& self.base as int + self.size as int <= MEM_4K_MASK as int + PAGE_SZ_4K as int
    }

    /// The 4K page base `p` lies in the BAR's outward-rounded page envelope: from the 4K page holding `base` up to the
    /// range's end.
    pub open spec fn envelope_contains(&self, p: PAddr) -> bool {
        &&& p % PAGE_SZ_4K == 0
        &&& self.base as int / PAGE_SZ_4K as int * PAGE_SZ_4K as int <= p as int
        &&& (p as int) < self.base as int + self.size as int
    }
}

pub const PCI_BAR_TABLE_CAPACITY: usize = 1024;

/// The memory BARs of every PCI function, filled once at boot and read-only afterwards. Sealed: verified code reads them
/// through `view` and can neither build nor change one.
// No exec code reads the entries yet; only the spec `view` does.
#[allow(dead_code)]
pub struct PciBarTable {
    entries: Array<PciBarEntry, PCI_BAR_TABLE_CAPACITY>,
    len: usize,
}

impl PciBarTable {
    /// The table's entries: the first `len` of its storage.
    pub closed spec fn view(&self) -> Seq<PciBarEntry> { self.entries.view().take(self.len as int) }

    /// Callable only from the unverified boot glue; `requires false` keeps verified code out.
    pub fn new(entries: Array<PciBarEntry, PCI_BAR_TABLE_CAPACITY>, len: usize) -> (ret: Self)
        requires false,
        ensures ret.view() == entries.view().take(len as int),
    {
        Self { entries, len }
    }
}
}
