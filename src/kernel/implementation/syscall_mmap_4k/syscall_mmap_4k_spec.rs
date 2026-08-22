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
        #![trigger pagetable.spec_resolve_mapping_4k_l1(
            spec_va2index(spec_va_add_range(va, i)).0,
            spec_va2index(spec_va_add_range(va, i)).1,
            spec_va2index(spec_va_add_range(va, i)).2,
            spec_va2index(spec_va_add_range(va, i)).3,
        )]
        i < len ==> {
            let mapped_va = spec_va_add_range(va, i);
            let indices = spec_va2index(mapped_va);
            &&& pagetable.mapping_4k().dom().contains(mapped_va)
            &&& pagetable.mapping_4k().spec_index(mapped_va).present
            &&& pagetable.mapping_4k().spec_index(mapped_va).write
            &&& !pagetable.mapping_4k().spec_index(mapped_va).execute_disable
            &&& pagetable.spec_resolve_mapping_4k_l1(
                indices.0, indices.1, indices.2, indices.3,
            ) is Some
            &&& pagetable.spec_resolve_mapping_4k_l1(
                indices.0, indices.1, indices.2, indices.3,
            )->0.perm.present
            &&& pagetable.spec_resolve_mapping_4k_l1(
                indices.0, indices.1, indices.2, indices.3,
            )->0.perm.kernel_present
        }
}

} // verus!
