use vstd::prelude::*;

verus! {
use crate::*;

impl PageTable<PT_TYPE> {
    /// EOF closure of `copy_kernel_entries_to_unpublished_root`: the copied root entries are the recorded kernel entries.
    pub(super) proof fn copy_kernel_entries_to_unpublished_root_eof(&self, target: PageMap)
        requires
            self.kernel_entries_wf(),
            forall|i: usize| #![trigger target.spec_index(i)] 0 <= i < self.kernel_l4_end ==> target.spec_index(i) =~= self.l4_table.view().spec_index(self.cr3).value().spec_index(i),
        ensures forall|i: usize| #![trigger target.spec_index(i)] 0 <= i < self.kernel_l4_end ==> target.spec_index(i) =~= self.kernel_entries.view().spec_index(i as int),
    { reveal(PageTable::kernel_entries_wf); }
}
} // verus!
