use vstd::prelude::*;
use crate::*;

verus! {

/// User-visible and physical result of a successful anonymous 4K mmap.
pub open spec fn mmap_4k_syscall_range_mapped(
    pagetable: PageTable<PT_TYPE>,
    va: VAddr,
    len: usize,
) -> bool {
    forall|i: usize|
        #![trigger pagetable.mapping_4k().dom().contains(
            spec_va_add_range(va, i),
        )]
        i < len ==> {
            let mapped_va = spec_va_add_range(va, i);
            &&& pagetable.mapping_4k().dom().contains(mapped_va)
            &&& pagetable.mapping_4k().spec_index(mapped_va).present
            &&& pagetable.mapping_4k().spec_index(mapped_va).write
            &&& !pagetable.mapping_4k().spec_index(mapped_va).execute_disable
        }
}

} // verus!
