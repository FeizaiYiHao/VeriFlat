use vstd::prelude::*;

verus! {

use crate::*;

/// Result of checking one complete 4K virtual-address range while its
/// process page table is write-locked.
#[derive(Clone, Copy)]
pub(super) enum Mmap4kRangeCheck {
    Empty,
    InUse,
    Invalid,
}

/// Every address in the suffix `[first, range.len)` is available for a new
/// 4K mapping.  `spec_4k_entry_useable` excludes an existing 4K leaf and any
/// covering 2M/1G leaf; absent intermediate tables are deliberately allowed.
pub open spec fn mmap_4k_range_empty_from(
    pagetable: PageTable<PT_TYPE>,
    range: &VaRange4K,
    first: int,
) -> bool {
    forall|i: int|
        #![trigger range.view().spec_index(i)]
        first <= i < range.len
        ==> {
            let indices = spec_va2index(range.view().spec_index(i));
            &&& pagetable.kernel_l4_end <= indices.0 < 512
            &&& 0 <= indices.1 < 512
            &&& 0 <= indices.2 < 512
            &&& 0 <= indices.3 < 512
            &&& pagetable.spec_4k_entry_useable(
                indices.0,
                indices.1,
                indices.2,
                indices.3,
            )
        }
}

pub open spec fn mmap_4k_range_empty(
    pagetable: PageTable<PT_TYPE>,
    range: &VaRange4K,
) -> bool {
    mmap_4k_range_empty_from(pagetable, range, 0)
}

/// The processed prefix is mapped with the requested permissions. Physical
/// addresses are intentionally existential here: each iteration obtains its
/// own allocator-selected data page.
pub open spec fn mmap_4k_range_mapped_prefix(
    pagetable: PageTable<PT_TYPE>,
    range: &VaRange4K,
    upper: int,
    write: bool,
    execute_disable: bool,
) -> bool {
    forall|i: int|
        #![trigger pagetable.mapping_4k().dom().contains(
            range.view().spec_index(i),
        )]
        #![trigger pagetable.mapping_4k().spec_index(range.view().spec_index(i))]
        0 <= i < upper
        ==> {
            &&& pagetable.mapping_4k().dom().contains(
                range.view().spec_index(i),
            )
            &&& pagetable.mapping_4k().spec_index(
                range.view().spec_index(i),
            ).present
            &&& pagetable.mapping_4k().spec_index(
                range.view().spec_index(i),
            ).write == write
            &&& pagetable.mapping_4k().spec_index(
                range.view().spec_index(i),
            ).execute_disable == execute_disable
        }
}

pub open spec fn mmap_4k_range_mapped(
    pagetable: PageTable<PT_TYPE>,
    range: &VaRange4K,
    write: bool,
    execute_disable: bool,
) -> bool {
    mmap_4k_range_mapped_prefix(
        pagetable,
        range,
        range.len as int,
        write,
        execute_disable,
    )
}

/// Public syscall postcondition expressed directly from the raw `(va, len)`
/// arguments, so callers do not need the syscall's local `VaRange4K` value.
pub open spec fn mmap_4k_raw_range_mapped(
    pagetable: PageTable<PT_TYPE>,
    va: VAddr,
    len: usize,
    write: bool,
    execute_disable: bool,
) -> bool
    decreases len,
{
    if len == 0 {
        true
    } else {
        &&& mmap_4k_raw_range_mapped(
            pagetable,
            va,
            (len - 1) as usize,
            write,
            execute_disable,
        )
        &&& {
            let i: usize = (len - 1) as usize;
            &&& pagetable.mapping_4k().dom().contains(
                spec_va_add_range(va, i),
            )
            &&& pagetable.mapping_4k().spec_index(
                spec_va_add_range(va, i),
            ).present
            &&& pagetable.mapping_4k().spec_index(
                spec_va_add_range(va, i),
            ).write == write
            &&& pagetable.mapping_4k().spec_index(
                spec_va_add_range(va, i),
            ).execute_disable == execute_disable
        }
    }
}

}
