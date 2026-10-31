use vstd::prelude::*;
use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use crate::*;

/// Memory of the page locks. Only raw addresses reach it; the page array's points-to tokens own its cells.
struct PageCells(UnsafeCell<MaybeUninit<[RwLock<Page, (), (), NO_KILL_STATE>; NUM_PAGES]>>);

// Every access goes through a cell's lock guard or its owning token.
unsafe impl Sync for PageCells {}

static PAGE_CELLS: PageCells = PageCells(UnsafeCell::new(MaybeUninit::uninit()));

verus! {
/// Address of the first page lock cell.
pub uninterp spec fn page_cells_base_spec() -> usize;

/// TCB: the address of the first page lock cell. Boot writes every cell in place before building the page array.
#[verifier::external_body]
pub fn page_cells_base() -> (ret: usize)
    ensures
        ret == page_cells_base_spec(),
{
    PAGE_CELLS.0.get() as usize
}
}
