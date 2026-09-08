use vstd::prelude::*;

use crate::*;

verus! {
/// No page object is present in this thread's held-lock ledger.
pub open spec fn mmap_4k_no_page_locks(lctx: &LocalContext) -> bool {
    lctx.page_lock_map().dom().is_empty()
}

/// The owner-lock context is ready to enter the 4K allocator only when no
/// page or allocator locks are held and every held owner lock orders below it.
pub open spec fn mmap_4k_allocation_ready(
    lctx: &LocalContext,
) -> bool {
    &&& mmap_4k_no_page_locks(lctx)
    &&& lctx.holds_no_allocator_locks(PageSize::SZ4k)
    &&& lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)
}

} // verus!
