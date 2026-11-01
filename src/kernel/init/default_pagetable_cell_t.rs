use vstd::prelude::*;
use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use crate::*;

/// Memory of the default page table's read-only node, outside the kernel object.
struct DefaultPagetableCell(UnsafeCell<MaybeUninit<ReadOnlyNode<PageTable<PT_TYPE>>>>);

// Init writes the cell once, before any reference to it exists; afterwards it is only read.
unsafe impl Sync for DefaultPagetableCell {}

static DEFAULT_PAGETABLE_CELL: DefaultPagetableCell = DefaultPagetableCell(UnsafeCell::new(MaybeUninit::uninit()));

verus! {
/// TCB: move `node` into the default page-table cell and return the cell; init only, once.
#[verifier::external_body]
pub(super) fn default_pagetable_cell_init(node: ReadOnlyNode<PageTable<PT_TYPE>>) -> (ret: &'static ReadOnlyNode<PageTable<PT_TYPE>>)
    ensures
        *ret == node,
{
    unsafe { &*(*DEFAULT_PAGETABLE_CELL.0.get()).write(node) }
}
}
