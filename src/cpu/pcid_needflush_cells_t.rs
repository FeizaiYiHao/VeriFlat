use vstd::prelude::*;
use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use crate::*;

/// Memory of the PCID needflush locks, one row of `PCID_MAX` cells per cpu. Only raw addresses reach it; the needflush
/// array's points-to tokens own its cells.
struct PcidNeedFlushCells(UnsafeCell<MaybeUninit<[[LockCell<PcidNeedFlush, (), Option<CpuId>, NO_KILL_STATE>; PCID_MAX]; NUM_CPUS]>>);

// Every access goes through a cell's lock guard or its owning token.
unsafe impl Sync for PcidNeedFlushCells {}

static PCID_NEEDFLUSH_CELLS: PcidNeedFlushCells = PcidNeedFlushCells(UnsafeCell::new(MaybeUninit::uninit()));

verus! {
/// Address of the first PCID needflush lock cell.
pub uninterp spec fn pcid_needflush_cells_base_spec() -> usize;

/// TCB: the address of the first PCID needflush lock cell. Boot writes every cell in place before building the
/// needflush array.
#[verifier::external_body]
pub fn pcid_needflush_cells_base() -> (ret: usize)
    ensures
        ret == pcid_needflush_cells_base_spec(),
{
    PCID_NEEDFLUSH_CELLS.0.get() as usize
}

impl TokenCellBase for LockCell<PcidNeedFlush, (), Option<CpuId>, NO_KILL_STATE> {
    open spec fn cell_base_spec() -> usize { pcid_needflush_cells_base_spec() }
    fn cell_base() -> (ret: usize) { pcid_needflush_cells_base() }
}
}
