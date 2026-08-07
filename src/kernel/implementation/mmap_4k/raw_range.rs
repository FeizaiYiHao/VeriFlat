use vstd::prelude::*;

use crate::*;

use super::syscall_def::{
    mmap_4k_range_mapped,
    mmap_4k_range_mapped_prefix,
    mmap_4k_raw_range_mapped,
};

verus! {

proof fn mmap_4k_range_mapped_implies_raw_prefix(
    pagetable: PageTable<PT_TYPE>,
    range: &VaRange4K,
    upper: usize,
    write: bool,
    execute_disable: bool,
)
    requires
        range.wf(),
        upper <= range.len,
        mmap_4k_range_mapped(pagetable, range, write, execute_disable),
    ensures
        mmap_4k_raw_range_mapped(
            pagetable,
            range.start,
            upper,
            write,
            execute_disable,
        ),
    decreases upper,
{
    if upper != 0 {
        assert(mmap_4k_raw_range_mapped(
            pagetable,
            range.start,
            (upper - 1) as usize,
            write,
            execute_disable,
        )) by { mmap_4k_range_mapped_implies_raw_prefix(pagetable, range, (upper - 1) as usize, write, execute_disable); };
        let i: usize = (upper - 1) as usize;
        assert(range.view().spec_index(i as int)
            == spec_va_add_range(range.start, i)) by { range.va_range_lemma(); };
    }
}

/// Re-express a mapped `VaRange4K` in terms of the syscall's raw arguments.
/// This is deliberately only a representation bridge: it does not open any
/// page-table invariant or reason about how the mappings were installed.
pub(super) proof fn mmap_4k_range_mapped_implies_raw(
    pagetable: PageTable<PT_TYPE>,
    range: &VaRange4K,
    write: bool,
    execute_disable: bool,
)
    requires
        range.wf(),
        mmap_4k_range_mapped(pagetable, range, write, execute_disable),
    ensures
        mmap_4k_raw_range_mapped(
            pagetable,
            range.start,
            range.len,
            write,
            execute_disable,
        ),
{
    assert(mmap_4k_raw_range_mapped(
        pagetable,
        range.start,
        range.len,
        write,
        execute_disable,
    )) by { mmap_4k_range_mapped_implies_raw_prefix(pagetable, range, range.len, write, execute_disable); };
}

} // verus!
