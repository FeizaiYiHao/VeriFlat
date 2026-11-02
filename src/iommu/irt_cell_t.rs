use vstd::prelude::*;
use vstd::simple_pptr::*;
use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use crate::*;

/// Memory of the IOMMU root-table lock. The lock is `#[repr(C)]` and 4K aligned, so the pinned table starts one 4K page
/// after the cell address. Only raw addresses reach it; the root-table lock's points-to token owns it.
struct IrtCell(UnsafeCell<MaybeUninit<LockCell<IommuRootTable, (), (), NO_KILL_STATE>>>);

// Every access goes through the lock guard or its owning token.
unsafe impl Sync for IrtCell {}

static IRT_CELL: IrtCell = IrtCell(UnsafeCell::new(MaybeUninit::uninit()));

verus! {
/// Address of the root-table lock cell.
pub uninterp spec fn irt_cell_base_spec() -> usize;

/// TCB: the address of the root-table lock cell.
#[verifier::external_body]
pub fn irt_cell_base() -> (ret: usize)
    ensures
        ret == irt_cell_base_spec(),
{
    IRT_CELL.0.get() as usize
}

impl TokenCellBase for LockCell<IommuRootTable, (), (), NO_KILL_STATE> {
    open spec fn cell_base_spec() -> usize { irt_cell_base_spec() }
    fn cell_base() -> (ret: usize) { irt_cell_base() }
}

/// TCB: write `lock` into the root-table lock cell and mint the cell's points-to token; init only, once.
#[verifier::external_body]
pub(crate) fn irt_cell_init(lock: LockCell<IommuRootTable, (), (), NO_KILL_STATE>) -> (ret: Tracked<LockObjPerm<IommuRootTable, (), (), NO_KILL_STATE>>)
    ensures
        ret.view().addr() == irt_cell_base_spec(),
        ret.view().is_init(),
        ret.view().value() == lock,
{
    unsafe { (IRT_CELL.0.get() as *mut LockCell<IommuRootTable, (), (), NO_KILL_STATE>).write(lock); }
    Tracked::assume_new()
}
}
